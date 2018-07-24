module Vale_gcm_load_xor_store_buffer_win

open X64.Machine_s
open X64.Memory_i
open X64.Vale.State_i
open X64.Vale.Decls_i
open X64.Util
open AES_s
open GCTR_i
open GCTR_s

val va_code_gcm_load_xor_store_buffer_win: unit -> va_code
let va_code_gcm_load_xor_store_buffer_win = va_code_gcm_load_xor_store_buffer_win

  //va_pre and va_post should correspond to the pre- and postconditions generated by Vale
let va_pre (va_b0:va_code) (va_s0:va_state) (stack_b:buffer64)
(plain_b:buffer128) (mask_b:buffer128) (cipher_b:buffer128) (offset:nat64) (num_blocks:(nat64)) (key:(aes_key_LE AES_128)) (iv:(quad32))  =
  ((va_require_total va_b0 (va_code_gcm_load_xor_store_buffer_win ()) va_s0) /\
    (va_get_ok va_s0) /\ (buffer_readable (va_get_mem va_s0) plain_b) /\ (buffer_readable
    (va_get_mem va_s0) mask_b) /\ (buffer_readable (va_get_mem va_s0) cipher_b) /\
    (valid_taint_buf128 plain_b (va_get_mem va_s0) (va_get_memTaint va_s0) Secret) /\
    (valid_taint_buf128 mask_b (va_get_mem va_s0) (va_get_memTaint va_s0) Secret) /\
    (valid_taint_buf128 cipher_b (va_get_mem va_s0) (va_get_memTaint va_s0) Secret) /\
    (locs_disjoint [(loc_buffer stack_b); (loc_buffer plain_b); (loc_buffer mask_b); (loc_buffer
    cipher_b)]) /\ (buffer_readable (va_get_mem va_s0) stack_b) /\ (buffer_length stack_b) >= 5 /\
    (valid_stack_slots (va_get_mem va_s0) (va_get_reg Rsp va_s0) stack_b 0 (va_get_memTaint va_s0)) /\ (va_get_reg Rcx
    va_s0) == (buffer_addr plain_b (va_get_mem va_s0)) /\ (va_get_reg Rdx va_s0) == (buffer_addr
    mask_b (va_get_mem va_s0)) /\ (va_get_reg R8 va_s0) == (buffer_addr cipher_b (va_get_mem
    va_s0)) /\ (va_get_reg R9 va_s0) == offset /\ (buffer_length plain_b) >= num_blocks /\
    (buffer_length cipher_b) == (buffer_length plain_b) /\ (buffer_length mask_b) == 1 /\ (let mask
    = (buffer128_read mask_b 0 (va_get_mem va_s0)) in let plain = (buffer128_as_seq (va_get_mem
    va_s0) plain_b) in let cipher = (buffer128_as_seq (va_get_mem va_s0) cipher_b) in offset <
    num_blocks /\ (buffer_addr plain_b (va_get_mem va_s0)) + offset `op_Multiply` 16 < pow2_64 /\
    (buffer_addr cipher_b (va_get_mem va_s0)) + offset `op_Multiply` 16 < pow2_64 /\ mask ==
    (aes_encrypt_BE AES_128 key (inc32 iv offset)) /\ (gctr_partial AES_128 offset plain cipher key
    iv)))


let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel) (stack_b:buffer64)
(plain_b:buffer128) (mask_b:buffer128) (cipher_b:buffer128) (offset:nat64) (num_blocks:(nat64)) (key:(aes_key_LE AES_128)) (iv:(quad32))  =
  va_pre va_b0 va_s0 stack_b plain_b mask_b cipher_b offset num_blocks key iv /\
((va_ensure_total va_b0 va_s0 va_sM va_fM) /\ (va_get_ok va_sM)
    /\ (buffer_readable (va_get_mem va_sM) plain_b) /\ (buffer_readable (va_get_mem va_sM) mask_b)
    /\ (buffer_readable (va_get_mem va_sM) cipher_b) /\ (valid_taint_buf128 plain_b (va_get_mem
    va_sM) (va_get_memTaint va_sM) Secret) /\ (valid_taint_buf128 mask_b (va_get_mem va_sM)
    (va_get_memTaint va_sM) Secret) /\ (valid_taint_buf128 cipher_b (va_get_mem va_sM)
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
    (modifies_buffer128 cipher_b (va_get_mem va_s0) (va_get_mem va_sM)) /\ (let mask =
    (buffer128_read mask_b 0 (va_get_mem va_s0)) in let plain = (buffer128_as_seq (va_get_mem
    va_sM) plain_b) in let old_cipher = (buffer128_as_seq (va_get_mem va_s0) cipher_b) in let
    cipher = (buffer128_as_seq (va_get_mem va_sM) cipher_b) in (gctr_partial AES_128 (offset + 1)
    plain cipher key iv) /\ (Seq.slice cipher 0 offset) == (Seq.slice old_cipher 0 offset)) /\ (va_state_eq
    va_sM ((va_update_mem va_sM (va_update_flags va_sM (va_update_xmm 15
    va_sM (va_update_xmm 14 va_sM (va_update_xmm 13 va_sM (va_update_xmm 12 va_sM (va_update_xmm 11
    va_sM (va_update_xmm 10 va_sM (va_update_xmm 9 va_sM (va_update_xmm 8 va_sM (va_update_xmm 7
    va_sM (va_update_xmm 6 va_sM (va_update_xmm 5 va_sM (va_update_xmm 4 va_sM (va_update_xmm 3
    va_sM (va_update_xmm 2 va_sM (va_update_xmm 1 va_sM (va_update_xmm 0 va_sM (va_update_reg R15
    va_sM (va_update_reg R14 va_sM (va_update_reg R13 va_sM (va_update_reg R12 va_sM (va_update_reg
    R11 va_sM (va_update_reg R10 va_sM (va_update_reg R9 va_sM (va_update_reg R8 va_sM
    (va_update_reg Rsp va_sM (va_update_reg Rbp va_sM (va_update_reg Rdi va_sM (va_update_reg Rsi
    va_sM (va_update_reg Rdx va_sM (va_update_reg Rcx va_sM (va_update_reg Rbx va_sM (va_update_reg
    Rax va_sM (va_update_ok va_sM va_s0))))))))))))))))))))))))))))))))))))))

val va_lemma_gcm_load_xor_store_buffer_win(va_b0:va_code) (va_s0:va_state) (stack_b:buffer64)
(plain_b:buffer128) (mask_b:buffer128) (cipher_b:buffer128) (offset:nat64) (num_blocks:(nat64)) (key:(aes_key_LE AES_128)) (iv:(quad32)) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 stack_b plain_b mask_b cipher_b offset num_blocks key iv )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM stack_b plain_b mask_b cipher_b offset num_blocks key iv ))

let va_lemma_gcm_load_xor_store_buffer_win = va_lemma_gcm_load_xor_store_buffer_win
