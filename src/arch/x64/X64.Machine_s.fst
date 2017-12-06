module X64.Machine_s

module M = Memory_i_s

unfold let nat32_max = Types_s.nat32_max
unfold let nat64_max = Types_s.nat64_max
unfold let nat128_max = Types_s.nat128_max

unfold let nat64 = Types_s.nat64
assume val int_to_nat64 : i:int -> n:nat64{0 <= i && i < nat64_max ==> i == n}
unfold let nat128 = Types_s.nat128

type reg =
  | Rax
  | Rbx
  | Rcx
  | Rdx
  | Rsi
  | Rdi
  | Rbp
  | Rsp
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15

type maddr =
  | MConst: n:int -> maddr
  | MReg: r:reg -> offset:int -> maddr
  | MIndex: base:reg -> scale:int -> index:reg -> offset:int -> maddr

type operand =
  | OConst: n:int -> operand
  | OReg: r:reg -> operand
  | OMem: m:maddr -> operand

type precode (t_ins:Type0) (t_ocmp:Type0) =
  | Ins: ins:t_ins -> precode t_ins t_ocmp
  | Block: block:list (precode t_ins t_ocmp) -> precode t_ins t_ocmp
  | IfElse: ifCond:t_ocmp -> ifTrue:precode t_ins t_ocmp -> ifFalse:precode t_ins t_ocmp -> precode t_ins t_ocmp
  | While: whileCond:t_ocmp -> whileBody:precode t_ins t_ocmp -> precode t_ins t_ocmp

let valid_dst (o:operand) : bool =
  not(OConst? o || (OReg? o && Rsp? (OReg?.r o)))

type dst_op = o:operand{valid_dst o}

type taint =
  | Public
  | Secret

type observation =
  | BranchPredicate: pred:bool -> observation
  | MemAccess: addr:nat64 -> observation
  | MemAccessOffset: base:nat64 -> index:nat64 -> observation

unfold let buffer8 = M.buffer (M.TBase M.TUInt8)
unfold let buffer16 = M.buffer (M.TBase M.TUInt16)
unfold let buffer32 = M.buffer (M.TBase M.TUInt32)
unfold let buffer64 = M.buffer (M.TBase M.TUInt64)
assume val buffer_addr : #t:M.typ -> b:M.buffer t -> GTot int

unfold let mem = M.mem
assume val valid_mem64 : ptr:int -> h:mem -> bool // is there a 64-bit word at address ptr?
assume val load_mem64 : ptr:int -> h:mem -> nat64 // the 64-bit word at ptr (if valid_mem64 holds)
assume val store_mem64 : ptr:int -> v:nat64 -> h:mem -> mem

assume val lemma_valid_mem64 : b:buffer64 -> i:nat -> h:mem -> Lemma
  (requires
    i < Seq.length (M.buffer_as_seq h b) /\
    M.buffer_readable h b
  )
  (ensures
    valid_mem64 (buffer_addr b + 8 `op_Multiply` i) h
  )

assume val lemma_load_mem64 : b:buffer64 -> i:int -> h:mem -> Lemma
  (requires
    i < Seq.length (M.buffer_as_seq h b) /\
    M.buffer_readable h b
  )
  (ensures
    load_mem64 (buffer_addr b + 8 `op_Multiply` i) h == M.buffer_read b i h
  )

assume val lemma_store_mem64 : b:buffer64 -> i:int -> v:nat64 -> h:mem -> Lemma
  (requires
    i < Seq.length (M.buffer_as_seq h b) /\
    M.buffer_readable h b
  )
  (ensures
    store_mem64 (buffer_addr b + 8 `op_Multiply` i) v h == M.buffer_write b i v h
  )

assume val lemma_store_load_mem64 : ptr:int -> v:nat64 -> h:mem -> Lemma
  (load_mem64 ptr (store_mem64 ptr v h) = v)

assume val lemma_frame_store_mem64: i:int -> v:nat64 -> h:mem -> Lemma (
  let h' = store_mem64 i v h in
  forall i'. i' <> i /\ valid_mem64 i h /\ valid_mem64 i' h ==> load_mem64 i' h = load_mem64 i' h')

assume val lemma_valid_store_mem64: i:int -> v:nat64 -> h:mem -> Lemma (
  let h' = store_mem64 i v h in
  forall j. valid_mem64 j h <==> valid_mem64 j h')
 
