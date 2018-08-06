module X64.Leakage_Ins

open X64.Machine_s
open X64.Taint_Semantics_s
open X64.Leakage_s
open X64.Leakage_Helpers

val check_if_ins_consumes_fixed_time: (ins:tainted_ins{not (is_xmm_ins ins)}) -> (ts:taintState) -> (res:(bool*taintState){ins_consumes_fixed_time ins ts res})

val lemma_ins_leakage_free: (ts:taintState) -> (ins:tainted_ins{not (is_xmm_ins ins)}) -> Lemma
 (let b, ts' = check_if_ins_consumes_fixed_time ins ts in
  (b2t b ==> isConstantTime (Ins ins) ts /\ isLeakageFree (Ins ins) ts ts'))
