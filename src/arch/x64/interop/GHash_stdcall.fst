module GHash_stdcall

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open AES_s
open GCTR_s
open GCM_s
open GCM_helpers_i
open GHash_i
#set-options "--z3rlimit 40"

open Vale_ghash_incremental_bytes_stdcall

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

let b8 = B.buffer UInt8.t

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map



//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (h_b:b8) (hash_b:b8) (input_b:b8) (num_bytes:nat64) : Lemma
  (requires pre_cond h0 h_b hash_b input_b num_bytes )
  (ensures (
(  let buffers = h_b::hash_b::input_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_h_b = addrs h_b in
  let addr_hash_b = addrs hash_b in
  let addr_input_b = addrs input_b in
  let regs = fun r -> begin match r with
    | rdi -> addr_h_b
    | rsi -> addr_hash_b
    | rdx -> addr_input_b
    | rcx -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) h_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) input_b;
  va_pre (va_code_ghash_incremental_bytes_stdcall ()) s0 h_b hash_b input_b num_bytes ))) =
  length_t_eq (TBase TUInt128) h_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) input_b;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (h_b:b8) (hash_b:b8) (input_b:b8) (num_bytes:nat64)  : Lemma
  (requires pre_cond va_s0.mem.hs h_b hash_b input_b num_bytes /\
    va_post (va_code_ghash_incremental_bytes_stdcall ()) va_s0 va_sM va_fM h_b hash_b input_b num_bytes )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs h_b hash_b input_b num_bytes ) =
  length_t_eq (TBase TUInt128) h_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) input_b;
  assert (Seq.equal
    (buffer128_as_seq (va_get_mem va_sM) input_b)
    (buffer_to_seq_quad input_b va_s0.mem.hs));
  ()

val ghost_ghash_incremental_bytes_stdcall: h_b:b8 -> hash_b:b8 -> input_b:b8 -> num_bytes:nat64 -> (h0:HS.mem{pre_cond h0 h_b hash_b input_b num_bytes }) -> GTot (h1:HS.mem{post_cond h0 h1 h_b hash_b input_b num_bytes })

let ghost_ghash_incremental_bytes_stdcall h_b hash_b input_b num_bytes h0 =
  let buffers = h_b::hash_b::input_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_h_b = addrs h_b in
  let addr_hash_b = addrs hash_b in
  let addr_input_b = addrs input_b in
  let regs = fun r -> begin match r with
    | rdi -> addr_h_b
    | rsi -> addr_hash_b
    | rdx -> addr_input_b
    | rcx -> num_bytes
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) h_b;
  length_t_eq (TBase TUInt128) hash_b;
  length_t_eq (TBase TUInt128) input_b;
  implies_pre h0 h_b hash_b input_b num_bytes ;
  let s1, f1 = va_lemma_ghash_incremental_bytes_stdcall (va_code_ghash_incremental_bytes_stdcall ()) s0 h_b hash_b input_b num_bytes  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs rbx == s1.regs rbx);
  assert(s0.regs rbp == s1.regs rbp);
  assert(s0.regs r12 == s1.regs r12);
  assert(s0.regs r13 == s1.regs r13);
  assert(s0.regs r14 == s1.regs r14);
  assert(s0.regs r15 == s1.regs r15);
  // Ensures that va_code_ghash_incremental_bytes_stdcall is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_ghash_incremental_bytes_stdcall ()) s0 s1 f1);
  implies_post s0 s1 f1 h_b hash_b input_b num_bytes ;
  s1.mem.hs

let ghash_incremental_bytes_stdcall h_b hash_b input_b num_bytes  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h h_b hash_b input_b (UInt64.v num_bytes) ) (ghost_ghash_incremental_bytes_stdcall h_b hash_b input_b (UInt64.v num_bytes) )
