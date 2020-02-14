module Atmel.Vale.Lemmas
open FStar.Mul
open Defs_s
open Prop_s
open Atmel.Machine_s
open Atmel.Vale.State
module S = Atmel.Semantics_s

unfold let code = S.code
unfold let codes = S.codes
unfold let ocmp = S.ocmp
unfold let fuel = nat

let cf (flags:int) : bool = S.cf (int_to_nat8 flags)
let update_cf (flags:int) (new_cf:bool) = S.update_cf (int_to_nat8 flags) new_cf

let eval_code (c:code) (s0:state) (f0:fuel) (s1:state) : prop0 =
  Some s1 == S.eval_code c f0 s0

let eval_ins (c:code) (s0:state) : Pure (state & fuel)
  (requires Ins? c)
  (ensures fun (sM, f0) ->
    eval_code c s0 f0 sM
  ) =
  let f0 = 0 in
  let (Some sM) = S.eval_code c f0 s0 in
  (sM, f0)

let eval_ocmp (s:state) (c:ocmp) : bool = S.eval_ocmp s c

val compute_merge_total (f0:fuel) (fM:fuel) : fuel

val lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) : Lemma
  (requires
    Cons? b0 /\
    eval_code (Cons?.hd b0) s0 f0 sM /\
    eval_code (Block (Cons?.tl b0)) sM fM sN
  )
  (ensures eval_code (Block b0) s0 (compute_merge_total f0 fM) sN)

val lemma_empty_total (s0:state) (bN:codes) : Pure (state & fuel)
  (requires True)
  (ensures (fun (sM, fM) ->
    s0 == sM /\
    eval_code (Block []) s0 fM sM
  ))
