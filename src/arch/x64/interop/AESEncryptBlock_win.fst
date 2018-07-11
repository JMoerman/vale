module AESEncryptBlock_win

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
module S8 = SecretByte
open Interop
open Words_s
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open BufferViewHelpers
#set-options "--z3rlimit 40"

open Vale_aes128_encrypt_block_win

assume val st_put (p:HS.mem -> Type0) (f:(h0:HS.mem{p h0}) -> GTot HS.mem) : Stack unit (fun h0 -> p h0) (fun h0 _ h1 -> f h0 == h1)

//The map from buffers to addresses in the heap, that remains abstract
assume val addrs: addr_map

//The initial registers and xmms
assume val init_regs:reg -> nat64
assume val init_xmms:xmm -> quad32

#set-options "--initial_fuel 6 --max_fuel 6 --initial_ifuel 2 --max_ifuel 2"
// TODO: Prove these two lemmas if they are not proven automatically
let implies_pre (h0:HS.mem) (output_b:s8) (input_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond h0 output_b input_b key keys_b /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b])
  (ensures (
B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b] /\ (  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == output_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == input_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == keys_b) then Secret else
    Public in
  let buffers = stack_b::output_b::input_b::keys_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_output_b = addrs output_b in
  let addr_input_b = addrs input_b in
  let addr_keys_b = addrs keys_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | rsp -> addr_stack
    | rcx -> addr_output_b
    | rdx -> addr_input_b
    | r8 -> addr_keys_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; trace = []; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  va_pre (va_code_aes128_encrypt_block_win ()) s0 stack_b output_b input_b (Ghost.reveal key) keys_b ))) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  ()

let implies_post (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (output_b:s8) (input_b:s8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:s8)  (stack_b:b8) : Lemma
  (requires pre_cond va_s0.mem.hs output_b input_b key keys_b /\ B.length stack_b == 32 /\ live va_s0.mem.hs stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b]/\
    va_post (va_code_aes128_encrypt_block_win ()) va_s0 va_sM va_fM stack_b output_b input_b (Ghost.reveal key) keys_b )
  (ensures post_cond va_s0.mem.hs va_sM.mem.hs output_b input_b key keys_b ) =
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  ()

val ghost_aes128_encrypt_block_win: output_b:s8 -> input_b:s8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:s8 ->  stack_b:b8 -> (h0:HS.mem{pre_cond h0 output_b input_b key keys_b /\ B.length stack_b == 32 /\ live h0 stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b]}) -> GTot (h1:HS.mem{post_cond h0 h1 output_b input_b key keys_b })

let ghost_aes128_encrypt_block_win output_b input_b key keys_b stack_b h0 =
  let taint_func (x:b8) : GTot taint =
    if StrongExcludedMiddle.strong_excluded_middle (x == output_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == input_b) then Secret else
    if StrongExcludedMiddle.strong_excluded_middle (x == keys_b) then Secret else
    Public in
  let buffers = stack_b::output_b::input_b::keys_b::[] in
  let (mem:mem) = {addrs = addrs; ptrs = buffers; hs = h0} in
  let addr_output_b = addrs output_b in
  let addr_input_b = addrs input_b in
  let addr_keys_b = addrs keys_b in
  let addr_stack:nat64 = addrs stack_b + 0 in
  let regs = fun r -> begin match r with
    | rsp -> addr_stack
    | rcx -> addr_output_b
    | rdx -> addr_input_b
    | r8 -> addr_keys_b
    | _ -> init_regs r end in
  let xmms = init_xmms in
  let s0 = {ok = true; regs = regs; xmms = xmms; flags = 0; mem = mem; trace = []; memTaint = create_valid_memtaint mem buffers taint_func} in
  length_t_eq (TBase TUInt64) stack_b;
  length_t_eq (TBase TUInt128) output_b;
  length_t_eq (TBase TUInt128) input_b;
  length_t_eq (TBase TUInt128) keys_b;
  implies_pre h0 output_b input_b key keys_b stack_b ;
  let s1, f1 = va_lemma_aes128_encrypt_block_win (va_code_aes128_encrypt_block_win ()) s0 stack_b output_b input_b (Ghost.reveal key) keys_b  in
  // Ensures that the Vale execution was correct
  assert(s1.ok);
  // Ensures that the callee_saved registers are correct
  assert(s0.regs rbx == s1.regs rbx);
  assert(s0.regs rbp == s1.regs rbp);
  assert(s0.regs rdi == s1.regs rdi);
  assert(s0.regs rsi == s1.regs rsi);
  assert(s0.regs rsp == s1.regs rsp);
  assert(s0.regs r12 == s1.regs r12);
  assert(s0.regs r13 == s1.regs r13);
  assert(s0.regs r14 == s1.regs r14);
  assert(s0.regs r15 == s1.regs r15);
  assert(s0.xmms 6 == s1.xmms 6);
  assert(s0.xmms 7 == s1.xmms 7);
  assert(s0.xmms 8 == s1.xmms 8);
  assert(s0.xmms 9 == s1.xmms 9);
  assert(s0.xmms 10 == s1.xmms 10);
  assert(s0.xmms 11 == s1.xmms 11);
  assert(s0.xmms 12 == s1.xmms 12);
  assert(s0.xmms 13 == s1.xmms 13);
  assert(s0.xmms 14 == s1.xmms 14);
  assert(s0.xmms 15 == s1.xmms 15);
  // Ensures that va_code_aes128_encrypt_block_win is actually Vale code, and that s1 is the result of executing this code
  assert (va_ensure_total (va_code_aes128_encrypt_block_win ()) s0 s1 f1);
  implies_post s0 s1 f1 output_b input_b key keys_b stack_b ;
  s1.mem.hs

let aes128_encrypt_block_win output_b input_b key keys_b  =
  push_frame();
  let (stack_b:b8) = B.alloca (UInt8.uint_to_t 0) (UInt32.uint_to_t 32) in
  let h0 = get() in
  st_put (fun h -> pre_cond h output_b input_b key keys_b /\ B.length stack_b == 32 /\ live h stack_b /\ buf_disjoint_from stack_b [output_b;input_b;keys_b]) (ghost_aes128_encrypt_block_win output_b input_b key keys_b stack_b);
  pop_frame()
