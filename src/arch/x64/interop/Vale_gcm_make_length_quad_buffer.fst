module Vale_gcm_make_length_quad_buffer

open X64.Machine_s
open X64.Memory_i
open X64.Vale.State_i
open X64.Vale.Decls_i
open X64.GCMencrypt
open Words_s

val va_code_gcm_make_length_quad_buffer: unit -> va_code
let va_code_gcm_make_length_quad_buffer = va_code_gcm_make_length_quad_buffer

//TODO: Fill this
  //va_pre and va_post should correspond to the pre- and postconditions generated by Vale
let va_pre (va_b0:va_code) (va_s0:va_state)
(plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:buffer128)  =
((va_require_total va_b0 (va_code_gcm_make_length_quad_buffer ()) va_s0) /\ (va_get_ok
    va_s0) /\ (buffer_readable (va_get_mem va_s0) b) /\ (va_get_reg Rdi va_s0) == plain_num_bytes
    /\ (va_get_reg Rsi va_s0) == auth_num_bytes /\ (va_get_reg Rdx va_s0) == (buffer_addr b
    (va_get_mem va_s0)) /\ (buffer_length b) == 1 /\ 8 `op_Multiply` plain_num_bytes < pow2_32 /\ 8
    `op_Multiply` auth_num_bytes < pow2_32)

let va_post (va_b0:va_code) (va_s0:va_state) (va_sM:va_state) (va_fM:va_fuel)
  (plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:buffer128)  =
  va_pre va_b0 va_s0 plain_num_bytes auth_num_bytes b /\
  ((va_ensure_total va_b0 va_s0 va_sM va_fM) /\ (va_get_ok va_sM)
    /\ (va_get_reg Rbx va_sM) == (va_get_reg Rbx va_s0) /\ (va_get_reg Rbp va_sM) == (va_get_reg
    Rbp va_s0) /\ (va_get_reg R12 va_sM) == (va_get_reg R12 va_s0) /\ (va_get_reg R13 va_sM) ==
    (va_get_reg R13 va_s0) /\ (va_get_reg R14 va_sM) == (va_get_reg R14 va_s0) /\ (va_get_reg R15
    va_sM) == (va_get_reg R15 va_s0) /\ (modifies_buffer128 b (va_get_mem va_s0) (va_get_mem
    va_sM)) /\ (buffer128_read b 0 (va_get_mem va_sM)) == (Mkfour (8 `op_Multiply` plain_num_bytes)
    0 (8 `op_Multiply` auth_num_bytes) 0) /\ (va_state_eq va_sM (va_update_mem va_sM
    (va_update_flags va_sM (va_update_xmm 15 va_sM (va_update_xmm 14 va_sM (va_update_xmm 13 va_sM
    (va_update_xmm 12 va_sM (va_update_xmm 11 va_sM (va_update_xmm 10 va_sM (va_update_xmm 9 va_sM
    (va_update_xmm 8 va_sM (va_update_xmm 7 va_sM (va_update_xmm 6 va_sM (va_update_xmm 5 va_sM
    (va_update_xmm 4 va_sM (va_update_xmm 3 va_sM (va_update_xmm 2 va_sM (va_update_xmm 1 va_sM
    (va_update_xmm 0 va_sM (va_update_reg R15 va_sM (va_update_reg R14 va_sM (va_update_reg R13
    va_sM (va_update_reg R12 va_sM (va_update_reg R11 va_sM (va_update_reg R10 va_sM (va_update_reg
    R9 va_sM (va_update_reg R8 va_sM (va_update_reg Rsp va_sM (va_update_reg Rbp va_sM
    (va_update_reg Rdi va_sM (va_update_reg Rsi va_sM (va_update_reg Rdx va_sM (va_update_reg Rcx
    va_sM (va_update_reg Rbx va_sM (va_update_reg Rax va_sM (va_update_ok va_sM
    va_s0)))))))))))))))))))))))))))))))))))))

val va_lemma_gcm_make_length_quad_buffer(va_b0:va_code) (va_s0:va_state)
  (plain_num_bytes:nat64) (auth_num_bytes:nat64) (b:buffer128) : Ghost ((va_sM:va_state) * (va_fM:va_fuel))
  (requires va_pre va_b0 va_s0 plain_num_bytes auth_num_bytes b )
  (ensures (fun (va_sM, va_fM) -> va_post va_b0 va_s0 va_sM va_fM plain_num_bytes auth_num_bytes b ))

let va_lemma_gcm_make_length_quad_buffer = va_lemma_gcm_make_length_quad_buffer

