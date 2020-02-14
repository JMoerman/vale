module Atmel.Vale.Lemmas
open FStar.Mul
open Atmel.Machine_s
open Atmel.Vale.State
module S = Atmel.Semantics_s

#reset-options "--initial_fuel 2 --max_fuel 2 --z3rlimit 20"

val increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code c s0 f0 sN /\ f0 <= fN)
  (ensures eval_code c s0 fN sN)
  (decreases %[f0; c])

val increase_fuels (c:codes) (s0:state) (f0:fuel) (sN:state) (fN:fuel) : Lemma
  (requires eval_code (Block c) s0 f0 sN /\ f0 <= fN)
  (ensures eval_code (Block c) s0 fN sN)
  (decreases %[f0; c])

let rec increase_fuel (c:code) (s0:state) (f0:fuel) (sN:state) (fN:fuel) =
  match c with
  | Ins ins -> ()
  | Block l -> increase_fuels l s0 f0 sN fN
and increase_fuels (c:codes) (s0:state) (f0:fuel) (sN:state) (fN:fuel) =
  match c with
  | [] -> ()
  | h::t ->
    (
      let Some s1 = S.eval_code h f0 s0 in
      increase_fuel h s0 f0 s1 fN;
      increase_fuels t s1 f0 sN fN
    )

let compute_merge_total (f0:fuel) (fM:fuel) =
  if f0 > fM then f0 else fM

let lemma_merge_total (b0:codes) (s0:state) (f0:fuel) (sM:state) (fM:fuel) (sN:state) =
  let f = if f0 > fM then f0 else fM in
  increase_fuel (Cons?.hd b0) s0 f0 sM f;
  increase_fuel (Block (Cons?.tl b0)) sM fM sN f

let lemma_empty_total (s0:state) (bN:codes) =
  (s0, 0)
