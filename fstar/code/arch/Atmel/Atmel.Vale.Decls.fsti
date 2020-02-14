module Atmel.Vale.Decls

// This interface should hide all of Semantics_s.
// (It should not refer to Semantics_s, directly or indirectly.)
// It should not refer to StateLemmas_i or Print_s,
// because they refer to Semantics_s.
// Regs_i and State_i are ok, because they do not refer to Semantics_s.

open FStar.Mul
open Defs_s
open Prop_s
open Atmel.Machine_s
open Atmel.Vale.State
open Types_s

val cf : (flags:int) -> bool
val update_cf (flags:int) (new_cf:bool) : (new_flags:int)

//unfold let va_subscript = Map.sel
unfold let va_subscript (#a:eqtype) (#b:Type) (x:Map.t a b) (y:a) : Tot b = Map.sel x y
unfold let va_update = Map.upd
unfold let va_hd = Cons?.hd
//unfold let va_tl = Cons?.tl // F* inlines "let ... = va_tl ..." more than we'd like; revised definition below suppresses this

// REVIEW: FStar.Pervasives.reveal_opaque doesn't include zeta, so it fails for recursive functions
// REVIEW: why is x' necessary to keep x from being normalized?
[@va_qattr] unfold let va_reveal_eq (#ax:Type) (s:string) (x x':ax) = norm [zeta; delta_only [s]] #ax x == x'
let va_reveal_opaque (s:string) = norm_spec [zeta; delta_only [s]]

// hide 'if' so that x and y get fully normalized
let va_if (#a:Type) (b:bool) (x:(_:unit{b}) -> a) (y:(_:unit{~b}) -> a) : a =
  if b then x () else y ()

// Type aliases
let va_int_at_least (k:int) = i:int{i >= k}
let va_int_at_most (k:int) = i:int{i <= k}
let va_int_range (k1 k2:int) = i:int{k1 <= i /\ i <= k2}
val ins : Type0
val ocmp : Type0
unfold let va_code = precode ins ocmp
unfold let va_codes = list va_code
let va_tl (cs:va_codes) : Ghost va_codes (requires Cons? cs) (ensures fun tl -> tl == Cons?.tl cs) = Cons?.tl cs
unfold let va_state = state
val va_fuel : Type0
unfold let va_operand_reg8 = reg
unfold let va_operand_iopr8 = imm8

val va_pbool : Type0
val va_ttrue (_:unit) : va_pbool
val va_ffalse (reason:string) : va_pbool
val va_pbool_and (x y:va_pbool) : va_pbool

noeq
type va_transformation_result = {
  success : va_pbool;
  result : va_code;
}
unfold let va_get_success (r:va_transformation_result) : va_pbool = r.success
unfold let va_get_result (r:va_transformation_result) : va_code = r.result

val mul_nat_helper (x y:nat) : Lemma (x * y >= 0)
[@va_qattr] unfold let va_mul_nat (x y:nat) : nat =
  mul_nat_helper x y;
  x * y

[@va_qattr] unfold let va_expand_state (s:state) : state = s

// Constructors
val va_fuel_default : unit -> va_fuel

// Evaluation
[@va_qattr] unfold let va_eval_reg8        (s:va_state) (r:reg)    : GTot nat8 = eval_reg r s
[@va_qattr] unfold let va_eval_iopr8        (s:va_state) (i:imm8)    : GTot nat8 = i

// Predicates
[@va_qattr] unfold let va_is_src_reg (r:reg) (s:va_state) = True
[@va_qattr] unfold let va_is_dst_reg (r:reg) (s:va_state) = True
[@va_qattr] unfold let va_is_src_reg8 (r:reg) (s:va_state) = va_is_src_reg r s
[@va_qattr] unfold let va_is_dst_reg8 (r:reg) (s:va_state) = va_is_dst_reg r s
[@va_qattr] unfold let va_is_src_iopr8 (i:imm8) (s:va_state) = True
[@va_qattr] unfold let va_is_dst_iopr8 (i:imm8) (s:va_state) = False

// Getters
[@va_qattr] unfold let va_get_ok (s:va_state) : bool = s.ok
[@va_qattr] unfold let va_get_flags (s:va_state) : int = s.flags
[@va_qattr] unfold let va_get_reg (r:reg) (s:va_state) : nat8 = eval_reg r s
[@va_qattr] unfold let va_get_mem (s:va_state) : memory = s.mem

[@va_qattr] let va_upd_ok (ok:bool) (s:state) : state = { s with ok = ok }
[@va_qattr] let va_upd_flags (flags:nat8) (s:state) : state = { s with flags = flags }
[@va_qattr] let va_upd_mem (mem:memory) (s:state) : state = { s with mem = mem }
[@va_qattr] let va_upd_reg (r:reg) (v:nat8) (s:state) : state = update_reg r v s

// Framing: va_update_foo means the two states are the same except for foo
[@va_qattr] unfold let va_update_ok (sM:va_state) (sK:va_state) : va_state = va_upd_ok sM.ok sK
[@va_qattr] unfold let va_update_flags (sM:va_state) (sK:va_state) : va_state = va_upd_flags sM.flags sK
[@va_qattr] unfold let va_update_reg (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_upd_reg r (eval_reg r sM) sK
[@va_qattr] unfold let va_update_mem (sM:va_state) (sK:va_state) : va_state = va_upd_mem sM.mem sK

[@va_qattr] unfold
let va_update_dst_reg (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_update_reg r sM sK

[@va_qattr] unfold
let va_update_operand_dst_reg8 (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_reg r sM sK

[@va_qattr] unfold
let va_update_operand_reg8 (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_update_dst_reg r sM sK

[@va_qattr] unfold
let va_update_register (r:reg) (sM:va_state) (sK:va_state) : va_state =
  va_update_reg r sM sK

unfold let va_value_reg8 = nat8
unfold let va_value_dst_reg8 = nat8

[@va_qattr]
let va_upd_operand_dst_reg8 (r:reg) (v:nat8) (s:state) : state =
  update_reg r v s

[@va_qattr]
let va_upd_operand_reg8 (r:reg) (v:nat8) (s:state) : state =
  update_reg r v s

val va_lemma_upd_update (sM:state) : Lemma
  (
    (forall (sK:state) (r:reg).{:pattern (va_update_operand_dst_reg8 r sM sK)} va_is_dst_reg8 r sK ==> va_update_operand_dst_reg8 r sM sK == va_upd_operand_dst_reg8 r (eval_reg r sM) sK) /\
    (forall (sK:state) (r:reg).{:pattern (va_update_operand_reg8 r sM sK)} va_is_dst_reg8 r sK ==> va_update_operand_reg8 r sM sK == va_upd_operand_reg8 r (eval_reg r sM) sK) )

// Constructors for va_codes
[@va_qattr] unfold let va_CNil () : va_codes = []
[@va_qattr] unfold let va_CCons (hd:va_code) (tl:va_codes) : va_codes = hd::tl

// Constructors for va_code
unfold let va_Block (block:va_codes) : va_code = Block block

unfold let va_get_block (c:va_code{Block? c}) : va_codes = Block?.block c

// Map syntax
// syntax for map accesses, m.[key] and m.[key] <- value
type map (key:eqtype) (value:Type) = Map.t key value
let (.[]) = Map.sel
let (.[]<-) = Map.upd

val eval_code (c:va_code) (s0:va_state) (f0:va_fuel) (sN:va_state) : prop0

[@va_qattr]
let va_state_eq (s0:va_state) (s1:va_state) : prop0 = state_eq s0 s1

val mem_inv (m:memory) : prop0

let state_inv (s:state) : prop0 = mem_inv s.mem

let va_require_total (c0:va_code) (c1:va_code) (s0:va_state) : prop0 =
  c0 == c1 /\ state_inv s0

let va_ensure_total (c0:va_code) (s0:va_state) (s1:va_state) (f1:va_fuel) : prop0 =
  eval_code c0 s0 f1 s1 /\ state_inv s1

val va_ins_lemma (c0:va_code) (s0:va_state) : Lemma
  (requires True)
  (ensures state_inv s0)

val eval_ocmp : s:va_state -> c:ocmp -> GTot bool
unfold let va_evalCond (b:ocmp) (s:va_state) : GTot bool = eval_ocmp s b

val va_compute_merge_total (f0:va_fuel) (fM:va_fuel) : va_fuel

val va_lemma_merge_total (b0:va_codes) (s0:va_state) (f0:va_fuel) (sM:va_state) (fM:va_fuel) (sN:va_state) : Ghost (fN:va_fuel)
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (va_Block (Cons?.tl b0)) sM fM sN
  )
  (ensures (fun fN ->
    fN == va_compute_merge_total f0 fM /\
    eval_code (va_Block b0) s0 fN sN
  ))

val va_lemma_empty_total (s0:va_state) (bN:va_codes) : Ghost (va_state & va_fuel)
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (va_Block []) s0 fM sM
  ))

val printer : Type0
val print_string : string -> FStar.All.ML unit
val print_header : printer -> FStar.All.ML unit
val print_proc : (name:string) -> (code:va_code) -> (label:int) -> (p:printer) -> FStar.All.ML int
val print_footer : printer -> FStar.All.ML unit
val masm : printer
val gcc : printer
