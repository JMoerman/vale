module Atmel.Vale.State
// This interface should not refer to Semantics_s

open FStar.Mul
open Defs_s
open Prop_s
open Atmel.Machine_s

unfold let state = Atmel.Machine_s.state

[@va_qattr]
unfold let eval_reg (r:reg) (s:state) : nat8 = s.regs r
[@va_qattr]
unfold let eval_mem (ptr:int) (s:state) : nat8 = load_mem8 ptr s.mem

[@va_qattr]
let eval_maddr (m:maddr) (s:state) : int =
  let open FStar.Mul in
    match m with
    | MConst n -> n
    | MReg reg offset -> eval_reg reg s + offset
    | MIndex base scale index offset -> eval_reg base s + scale * (eval_reg index s) + offset

[@va_qattr]
let to_nat8 (i:int) : nat8 =
  if 0 <= i && i < 0x100 then i else int_to_nat8 i

[@va_qattr]
let update_reg (r:reg) (v:nat8) (s:state) : state =
  { s with regs = regs_make (fun (r':reg) -> if r = r' then v else s.regs r') }

[@va_qattr]
let update_mem (ptr:int) (v:nat8) (s:state) : state = { s with mem = store_mem8 ptr v s.mem }

[@va_qattr]
let state_eq (s0:state) (s1:state) : prop0 =
  s0.ok == s1.ok /\
  Regs.equal s0.regs s1.regs /\
  s0.flags == s1.flags /\
  s0.mem == s1.mem

