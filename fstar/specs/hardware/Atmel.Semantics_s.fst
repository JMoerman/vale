module Atmel.Semantics_s

open FStar.Mul
open Defs_s
open Atmel.Machine_s
open Words_s
open Words.Two_s
open Words.Four_s
open Types_s
open FStar.Seq.Base

let (.[]) = Map.sel
let (.[]<-) = Map.upd

type ins =
  | Mov8       : rd:reg -> rr:reg -> ins
  | LoadImm8   : rd:reg -> k:imm8 -> ins
  | Mul8       : rd:reg -> rr:reg -> ins
  | Add8       : rd:reg -> rr:reg -> ins
  | AddCarry8  : rd:reg -> rr:reg -> ins
  | Sub8       : rd:reg -> rr:reg -> ins
  | SubBorrow8 : rd:reg -> rr:reg -> ins
  | SubImm8    : rd:reg -> k:imm8 -> ins
  | SubCImm8   : rd:reg -> k:imm8 -> ins
  | Neg        : rd:reg           -> ins
  | Inc        : rd:reg           -> ins
  | Dec        : rd:reg           -> ins
  | Mov16      : rd:reg -> rr:reg -> ins

type ocmp =
  | OBrne : ocmp

type code = precode ins ocmp
type codes = list code

assume val havoc : state -> ins -> nat8

unfold let eval_reg (r:reg) (s:state) : nat8 = s.regs r
unfold let eval_mem (ptr:int) (s:state) : nat8 = load_mem8 ptr s.mem

unfold
let reg_valid_word (r:reg) (s:state) : bool
= r <> R15

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> (eval_reg reg s) + offset
    | MIndex base scale index offset -> (eval_reg base s) + scale * (eval_reg index s) + offset

let eval_ocmp (s:state) (c:ocmp) :bool =
  match c with
  | OBrne -> 0 = havoc s (Dec R0)

let update_reg' (r:reg) (v:nat8) (s:state) : state =
  { s with regs = regs_make (fun (r':reg) -> if r' = r then v else s.regs r') }

val mod_8: (n:nat{n < pow2_8}) -> nat8
let mod_8 n = n % 0x100

let update_mem (ptr:int) (v:nat8) (s:state) : state =
  { s with mem = store_mem8 ptr v s.mem }

let update_reg_preserve_flags' (r:reg) (v:nat8) (s:state) : state =
  update_reg' r v s

// Default version havocs flags

// REVIEW: Will we regret exposing a mod here?  Should flags be something with more structure?
let cf (flags:nat8) : bool =
  flags % 2 = 1

//unfold let bit11 = normalize_term (pow2 11)
let _ = assert (2048 == normalize_term (pow2 11))

let update_cf (flags:nat8) (new_cf:bool) : (new_flags:nat8{cf new_flags == new_cf}) =
  if new_cf then
    if not (cf flags) then
      flags + 1
    else
      flags
  else
    if (cf flags) then
      flags - 1
    else
      flags

// Define a stateful monad to simplify defining the instruction semantics
let st (a:Type) = state -> a & state

unfold
let return (#a:Type) (x:a) :st a =
  fun s -> x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) :st b =
fun s0 ->
  let x, s1 = m s0 in
  let y, s2 = f x s1 in
  y, {s2 with ok=s0.ok && s1.ok && s2.ok}

unfold
let get :st state =
  fun s -> s, s

unfold
let set (s:state) :st unit =
  fun _ -> (), s

unfold
let fail :st unit =
  fun s -> (), {s with ok=false}

unfold
let check_imm (valid:bool) : st unit =
  if valid then
    return ()
  else
    fail

unfold
let check (valid: state -> bool) : st unit =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let run (f:st unit) (s:state) : state = snd (f s)

// Monadic update operations
unfold
let update_reg_preserve_flags (dst:reg) (v:nat8) :st unit =
  s <-- get;
  set (update_reg_preserve_flags' dst v s)

// Default version havocs flags
unfold
let update_reg (r:reg) (v:nat8) :st unit =
  s <-- get;
  set (update_reg' r v s)

let update_flags (new_flags:nat8) :st unit =
  s <-- get;
  set ( { s with flags = new_flags } )

//let update_cf_of (new_cf new_of:bool) :st unit =
//  s <-- get;
//  set ( { s with flags = update_cf s.flags new_cf } )

// Core definition of instruction semantics
let eval_ins (ins:ins) : st unit =
  s <-- get;
  match ins with
  | Mov8 rd rr ->
    update_reg_preserve_flags rd (eval_reg rr s)

  | LoadImm8 rd k ->
    update_reg_preserve_flags rd (int_to_nat8 k)

  | Mul8 rd rr ->
    let rdv = eval_reg rd s in
    let rrv = eval_reg rr s in
    let hi = FStar.UInt.mul_div #8 rdv rrv in
    let lo = FStar.UInt.mul_mod #8 rdv rrv in
    let new_carry = hi >= 128 in
    update_reg R0 lo;;
    update_reg R1 hi;;
    update_flags (update_cf s.flags new_carry)

  | Add8 rd rr ->
    let sum = (eval_reg rd s) + (eval_reg rr s) in
    let new_carry = sum >= pow2_8 in
    update_reg rd (sum % pow2_8);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)

  | AddCarry8 rd rr ->
    let old_carry = if cf(s.flags) then 1 else 0 in
    let sum = (eval_reg rd s) + (eval_reg rr s) + old_carry in
    let new_carry = sum >= pow2_8 in
    update_reg rd (sum % pow2_8);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)

  | Sub8 rd rr ->
    let sum = (eval_reg rd s) - (eval_reg rr s) in
    let new_carry = sum <= -1 in
    update_reg rd (sum % pow2_8);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)

  | SubBorrow8 rd rr ->
    let old_carry = if cf(s.flags) then 1 else 0 in
    let sum = (eval_reg rd s) - (eval_reg rr s) - old_carry in
    let new_carry = sum <= -1 in
    update_reg rd (sum % pow2_8);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)

  | SubImm8 rd k ->
    let sum = (eval_reg rd s) -k  in
    let new_carry = sum <= -1 in
    update_reg rd (sum % pow2_8);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)

  | SubCImm8 rd k ->
    let old_carry = if cf(s.flags) then 1 else 0 in
    let sum = (eval_reg rd s) -k - old_carry in
    let new_carry = sum <= -1 in
    update_reg rd (sum % pow2_8);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)

  | Neg rd ->
    let r = (0 - (eval_reg rd s)) % pow2_8 in
    let new_carry = (r = 0) in
    update_reg rd r;;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)

  | Inc rd ->
    let sum = (eval_reg rd s) + 1 in
    let new_carry = sum >= pow2_8 in
    update_reg rd (sum % pow2_8);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)

  | Dec rd ->
    let sum = (eval_reg rd s) - 1 in
    let new_carry = sum <= -1 in
    update_reg rd (sum % pow2_8);;
    update_flags (havoc s ins);;
    update_flags (update_cf s.flags new_carry)

  | Mov16 rd rr ->
    check (reg_valid_word rd);;
    check (reg_valid_word rr);;
    let rdh = next_reg (rd) in
    let rrh = next_reg (rr) in
    let rrv = eval_reg rr s in
    let rrhv = eval_reg rrh s in
    update_reg rd rrv;;
    update_reg rdh rrhv

(*
 * These functions return an option state
 * None case arises when the while loop runs out of fuel
 *)
// TODO: IfElse and While should havoc the flags
val eval_code:  c:code           -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; c])
val eval_codes: l:codes          -> fuel:nat -> s:state -> Tot (option state) (decreases %[fuel; l])

let rec eval_code c fuel s =
  match c with
  | Ins ins                       -> Some (run (eval_ins ins) s)
  | Block l                       -> eval_codes l fuel s

and eval_codes l fuel s =
  match l with
  | []   -> Some s
  | c::tl ->
    let s_opt = eval_code c fuel s in
    if None? s_opt then None else eval_codes tl fuel (Some?.v s_opt)
