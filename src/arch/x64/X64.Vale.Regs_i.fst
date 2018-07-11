module X64.Vale.Regs_i
open X64.Machine_s
open FStar.FunctionalExtensionality

let equal regs1 regs2 = regs1 == regs2
let lemma_equal_intro regs1 regs2 = Map16_i.lemma_equal regs1 regs2
let lemma_equal_elim regs1 regs2 = ()

