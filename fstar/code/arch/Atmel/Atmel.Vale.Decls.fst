module Atmel.Vale.Decls
open FStar.Mul
open Atmel.Machine_s
open Atmel.Vale
open Atmel.Vale.State
open FStar.UInt
module S = Atmel.Semantics_s
module P = Atmel.Print_s

let cf = Lemmas.cf
let update_cf = Lemmas.update_cf
let ins = S.ins
type ocmp = S.ocmp
type va_fuel = nat

type va_pbool = Vale.Def.PossiblyMonad.pbool
let va_ttrue () = Vale.Def.PossiblyMonad.ttrue
let va_ffalse = Vale.Def.PossiblyMonad.ffalse
let va_pbool_and x y = Vale.Def.PossiblyMonad.((&&.)) x y

let mul_nat_helper x y =
  FStar.Math.Lemmas.nat_times_nat_is_nat x y

let va_fuel_default () = 0

let va_lemma_upd_update sM =
  ()

let eval_code = Lemmas.eval_code

let mem_inv m = True
let va_ins_lemma c0 s0 = ()

let eval_ocmp = Lemmas.eval_ocmp

unfold let va_eval_ins = Lemmas.eval_ins

let va_compute_merge_total = Lemmas.compute_merge_total
let va_lemma_merge_total b0 s0 f0 sM fM sN = Lemmas.lemma_merge_total b0 s0 f0 sM fM sN; Lemmas.compute_merge_total f0 fM
let va_lemma_empty_total = Lemmas.lemma_empty_total

let printer = P.printer
let print_string = FStar.IO.print_string
let print_header = P.print_header
let print_proc = P.print_proc
let print_footer = P.print_footer
let masm = P.masm
let gcc = P.gcc
