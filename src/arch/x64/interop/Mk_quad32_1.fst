module Mk_quad32_1

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
#set-options "--z3rlimit 40"

open Vale_mk_quad32_lo0_be_1_buffer

assume val st_put (h:HS.mem) (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0 /\ h == h0) (fun h0 _ h1 -> h == h0 /\ f h == h1)

let b8 = B.buffer UInt8.t

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map



//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 4 --max_fuel 4 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (b:b8) : Lemma
  (requires pre_cond h0 b )
  (ensures (
(  let buffers = b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_b = addrs b in
  let regs = fun r -> begin match r with
    | rdi -> addr_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) b;
  va_pre (va_code_mk_quad32_lo0_be_1_buffer ()) s0 b ))) =
  length_t_eq (TBase TUInt128) b;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (b:b8)  : Lemma
  (requires pre_cond va_s0.mem.hs b /\
    va_post (va_code_mk_quad32_lo0_be_1_buffer ()) va_s0 va_sM va_fM b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs b ) =
  length_t_eq (TBase TUInt128) b;
  let b128 = BV.mk_buffer_view b Views.view128 in
  assert (Seq.equal (buffer_as_seq (va_get_mem va_sM) b) (BV.as_seq va_sM.mem.hs b128));
  BV.as_seq_sel va_sM.mem.hs b128 0;
  assert (Seq.equal (buffer_as_seq (va_get_mem va_s0) b) (BV.as_seq va_s0.mem.hs b128));
  BV.as_seq_sel va_s0.mem.hs b128 0;  
  ()

val ghost_mk_quad32_lo0_be_1_buffer: b:b8 -> (h0:HS.mem{pre_cond h0 b }) -> GTot (h1:HS.mem{post_cond h0 h1 b })

let ghost_mk_quad32_lo0_be_1_buffer b h0 =
  let buffers = b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_b = addrs b in
  let regs = fun r -> begin match r with
    | rdi -> addr_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem} in
  length_t_eq (TBase TUInt128) b;
  implies_pre h0 b ;
  let s1, f1 = va_lemma_mk_quad32_lo0_be_1_buffer (va_code_mk_quad32_lo0_be_1_buffer ()) s0 b  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs rbx == s1.regs rbx);
  assert(s0.regs rbp == s1.regs rbp);
  assert(s0.regs r12 == s1.regs r12);
  assert(s0.regs r13 == s1.regs r13);
  assert(s0.regs r14 == s1.regs r14);
  assert(s0.regs r15 == s1.regs r15);
  // Ensures that va_code_mk_quad32_lo0_be_1_buffer is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_mk_quad32_lo0_be_1_buffer ()) s0 s1 f1);
  implies_post s0 s1 f1 b ;
  s1.mem.hs

let mk_quad32_lo0_be_1_buffer b  =
  let h0 = get() in
  st_put h0 (fun h -> pre_cond h b ) (ghost_mk_quad32_lo0_be_1_buffer b )
