module Vale_ghash_incremental_bytes_stdcall_win

open X64.Machine_s
open X64.Memory_i
open X64.Vale.State_i
open X64.Vale.Decls_i
open Types_s
open GCTR_s
open GCM_helpers_i
open GHash_i
open X64.GHash

val va_code_ghash_incremental_bytes_stdcall_win: unit -> va_code
let va_code_ghash_incremental_bytes_stdcall_win = va_code_ghash_incremental_bytes_stdcall_win

  //va_pre and va_post should correspond to the pre- and postconditions generated by Vale
let va_pre (va_b0:va_code) (va_s0:va_state) (stack_b:buffer64)
(h_b:buffer128) (hash_b:buffer128) (input_b:buffer128) (num_bytes:nat64)  =
  ((va_require_total va_b0 (va_code_ghash_incremental_bytes_stdcall_win ()) va_s0) /\
    (va_get_ok va_s0) /\ (validSrcAddrs128 (va_get_mem va_s0) (va_get_reg R8 va_s0) input_b
    (bytes_to_quad_size num_bytes) (va_get_memTaint va_s0) Secret) /\ (buffer_readable (va_get_mem
    va_s0) h_b) /\ (buffer_readable (va_get_mem va_s0) hash_b) /\ (valid_taint_buf128 h_b
    (va_get_mem va_s0) (va_get_memTaint va_s0) Secret) /\ (valid_taint_buf128 hash_b (va_get_mem
    va_s0) (va_get_memTaint va_s0) Secret) /\ (locs_disjoint [(loc_buffer stack_b); (loc_buffer
    h_b); (loc_buffer hash_b); (loc_buffer input_b)]) /\ (buffer_readable (va_get_mem va_s0)
    stack_b) /\ (buffer_readable (va_get_mem va_s0) h_b) /\ (buffer_readable (va_get_mem va_s0)
    hash_b) /\ (buffer_readable (va_get_mem va_s0) input_b) /\ (buffer_length stack_b) >= 10 /\
    (valid_stack_slots (va_get_mem va_s0) (va_get_reg Rsp va_s0) stack_b 5) /\ (va_get_reg Rcx
    va_s0) == (buffer_addr h_b (va_get_mem va_s0)) /\ (va_get_reg Rdx va_s0) == (buffer_addr hash_b
    (va_get_mem va_s0)) /\ (va_get_reg R8 va_s0) == (buffer_addr input_b (va_get_mem va_s0)) /\
    (va_get_reg R9 va_s0) == num_bytes /\ (num_bytes > 0 ==> (va_get_reg R8 va_s0) + 16
    `op_Multiply` (bytes_to_quad_size num_bytes) < pow2_64) /\ (num_bytes > 0 ==> (buffer_length
    input_b) == (bytes_to_quad_size num_bytes)) /\ (buffer_length h_b) > 0 /\ (buffer_length
    hash_b) > 0)
    
let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (stack_b:buffer64)
(h_b:buffer128) (hash_b:buffer128) (input_b:buffer128) (num_bytes:nat64)  =
  ((va_ensure_total va_b0 va_s0 va_sM va_fM) /\ (va_get_ok va_sM)
    /\ (validSrcAddrs128 (va_get_mem va_sM) (va_get_reg R8 va_s0) input_b (bytes_to_quad_size
    num_bytes) (va_get_memTaint va_sM) Secret) /\ (buffer_readable (va_get_mem va_sM) h_b) /\
    (buffer_readable (va_get_mem va_sM) hash_b) /\ (valid_taint_buf128 h_b (va_get_mem va_sM)
    (va_get_memTaint va_sM) Secret) /\ (valid_taint_buf128 hash_b (va_get_mem va_sM)
    (va_get_memTaint va_sM) Secret) /\ (va_get_reg Rbx va_sM) == (va_get_reg Rbx va_s0) /\
    (va_get_reg Rbp va_sM) == (va_get_reg Rbp va_s0) /\ (va_get_reg Rdi va_sM) == (va_get_reg Rdi
    va_s0) /\ (va_get_reg Rsi va_sM) == (va_get_reg Rsi va_s0) /\ (va_get_reg Rsp va_sM) ==
    (va_get_reg Rsp va_s0) /\ (va_get_reg R12 va_sM) == (va_get_reg R12 va_s0) /\ (va_get_reg R13
    va_sM) == (va_get_reg R13 va_s0) /\ (va_get_reg R14 va_sM) == (va_get_reg R14 va_s0) /\
    (va_get_reg R15 va_sM) == (va_get_reg R15 va_s0) /\ (va_get_xmm 6 va_sM) == (va_get_xmm 6
    va_s0) /\ (va_get_xmm 7 va_sM) == (va_get_xmm 7 va_s0) /\ (va_get_xmm 8 va_sM) == (va_get_xmm 8
    va_s0) /\ (va_get_xmm 9 va_sM) == (va_get_xmm 9 va_s0) /\ (va_get_xmm 10 va_sM) == (va_get_xmm
    10 va_s0) /\ (va_get_xmm 11 va_sM) == (va_get_xmm 11 va_s0) /\ (va_get_xmm 12 va_sM) ==
    (va_get_xmm 12 va_s0) /\ (va_get_xmm 13 va_sM) == (va_get_xmm 13 va_s0) /\ (va_get_xmm 14
    va_sM) == (va_get_xmm 14 va_s0) /\ (va_get_xmm 15 va_sM) == (va_get_xmm 15 va_s0) /\
    (modifies_mem (loc_union (loc_buffer hash_b) (loc_buffer stack_b)) (va_get_mem va_s0)
    (va_get_mem va_sM)) /\ (buffer_readable (va_get_mem va_sM) h_b) /\ (buffer_readable (va_get_mem
    va_sM) hash_b) /\ (buffer_readable (va_get_mem va_sM) input_b) /\ (num_bytes == 0 ==>
    (buffer128_read hash_b 0 (va_get_mem va_sM)) == (buffer128_read hash_b 0 (va_get_mem va_s0)))
    /\ (let input_bytes = (slice_work_around (le_seq_quad32_to_bytes (buffer128_as_seq (va_get_mem
    va_sM) input_b)) num_bytes) in let padded_bytes = (pad_to_128_bits input_bytes) in let
    input_quads = (le_bytes_to_seq_quad32 padded_bytes) in let h = (buffer128_read h_b 0
    (va_get_mem va_s0)) in let old_io = (buffer128_read hash_b 0 (va_get_mem va_s0)) in let io =
    (buffer128_read hash_b 0 (va_get_mem va_sM)) in num_bytes > 0 ==> (l_and ((Seq.length input_quads)
    > 0) (io == (ghash_incremental h old_io input_quads)))) /\ (va_state_eq va_sM (va_update_trace
    va_sM (va_update_mem va_sM (va_update_flags va_sM (va_update_xmm 15 va_sM (va_update_xmm 14
    va_sM (va_update_xmm 13 va_sM (va_update_xmm 12 va_sM (va_update_xmm 11 va_sM (va_update_xmm 10
    va_sM (va_update_xmm 9 va_sM (va_update_xmm 8 va_sM (va_update_xmm 7 va_sM (va_update_xmm 6
    va_sM (va_update_xmm 5 va_sM (va_update_xmm 4 va_sM (va_update_xmm 3 va_sM (va_update_xmm 2
    va_sM (va_update_xmm 1 va_sM (va_update_xmm 0 va_sM (va_update_reg R15 va_sM (va_update_reg R14
    va_sM (va_update_reg R13 va_sM (va_update_reg R12 va_sM (va_update_reg R11 va_sM (va_update_reg
    R10 va_sM (va_update_reg R9 va_sM (va_update_reg R8 va_sM (va_update_reg Rsp va_sM
    (va_update_reg Rbp va_sM (va_update_reg Rdi va_sM (va_update_reg Rsi va_sM (va_update_reg Rdx
    va_sM (va_update_reg Rcx va_sM (va_update_reg Rbx va_sM (va_update_reg Rax va_sM (va_update_ok
    va_sM va_s0))))))))))))))))))))))))))))))))))))))

val va_lemma_ghash_incremental_bytes_stdcall_win(va_b0:va_code) (va_s0:va_state) (stack_b:buffer64)
(h_b:buffer128) (hash_b:buffer128) (input_b:buffer128) (num_bytes:nat64) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 stack_b h_b hash_b input_b num_bytes )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM stack_b h_b hash_b input_b num_bytes ))

let va_lemma_ghash_incremental_bytes_stdcall_win = va_lemma_ghash_incremental_bytes_stdcall_win
