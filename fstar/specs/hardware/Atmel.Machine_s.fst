module Atmel.Machine_s
open FStar.Mul
open Defs_s

unfold let pow2_8 = Words_s.pow2_8
unfold let pow2_32 = Words_s.pow2_32
unfold let pow2_64 = Words_s.pow2_64
unfold let pow2_128 = Words_s.pow2_128

unfold let nat8 = Words_s.nat8
unfold let nat16 = Words_s.nat16
unfold let nat32 = Words_s.nat32
unfold let nat64 = Words_s.nat64
let int_to_nat8 (i:int) : n:nat8{0 <= i && i < pow2_8 ==> i == n} =
  Words_s.int_to_natN pow2_8 i

type reg =
  | R0
  | R1
  | R2
  | R3
  | R4
  | R5
  | R6
  | R7
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15

type imm8 = i:int{0 <= i && i < 256}

type mem_entry =
| Mem8: v:nat8 -> mem_entry
| Mem16: v:nat16 -> mem_entry
| Mem32: v:nat32 -> mem_entry
| Mem64: v:nat64 -> mem_entry

type memory = Map.t int mem_entry

let regs_t = FStar.FunctionalExtensionality.restricted_t reg (fun _ -> nat8)
[@va_qattr] unfold let regs_make (f:reg -> nat8) : regs_t = FStar.FunctionalExtensionality.on_dom reg f

noeq type state = {
  ok: bool;
  regs: regs_t;
  flags: nat8;
  mem: memory;
}

unfold
let next_reg (r:reg): reg
= match r with
  | R0 -> R1
  | R1 -> R2
  | R2 -> R3
  | R3 -> R4
  | R4 -> R5
  | R5 -> R6
  | R6 -> R7
  | R7 -> R8
  | R8 -> R9
  | R9 -> R10
  | R10 -> R11
  | R11 -> R12
  | R12 -> R13
  | R13 -> R14
  | R14 -> R15
  | R15 -> R0

assume val load_mem8 (addr:int) (m:memory) : Pure nat8
  (requires True)
  (ensures fun n -> match Map.sel m addr with Mem8 v -> v == n | _ -> True)

let store_mem8 (addr:int) (v:nat8) (m:memory) : memory =
  Map.upd m addr (Mem8 v)

type maddr =
  | MConst: n:int -> maddr
  | MReg: r:reg -> offset:int -> maddr
  | MIndex: base:reg -> scale:int -> index:reg -> offset:int -> maddr

type precode (t_ins:Type0) (t_ocmp:Type0) =
  | Ins: ins:t_ins -> precode t_ins t_ocmp
  | Block: block:list (precode t_ins t_ocmp) -> precode t_ins t_ocmp
