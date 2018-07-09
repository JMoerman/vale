module GCTR

open LowStar.Buffer
module B = LowStar.Buffer
module BV = LowStar.BufferView
open LowStar.Modifies
module M = LowStar.Modifies
open LowStar.ModifiesPat
open FStar.HyperStack.ST
module HS = FStar.HyperStack
open Interop
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
open Types_s
open Types_i
open Words_s
open Words.Seq_s
open AES_s
open GCTR_s
open GCTR_i
open GCM_s
open GCM_helpers_i
open GHash_i


let rec loc_locs_disjoint_rec (l:b8) (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> M.loc_disjoint (M.loc_buffer l) (M.loc_buffer h) /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let locs_disjoint (ls:list b8) : Type0 = normalize (locs_disjoint_rec ls)

let buffer_to_seq_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

let buffer_to_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let keys_match (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:B.buffer UInt8.t { B.length keys_b % 16 == 0 }) (h:HS.mem) =
  let keys128_b = BV.mk_buffer_view keys_b Views.view128 in
  let round_keys = key_to_round_keys_LE AES_128 (Ghost.reveal key) in
  BV.as_seq h keys128_b == round_keys

open FStar.Mul

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (plain_b:b8) (num_bytes:nat32) (iv_old:Ghost.erased (quad32)) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8) = live h plain_b /\ live h iv_b /\ live h keys_b /\ live h cipher_b /\ locs_disjoint [plain_b;iv_b;keys_b;cipher_b] /\ length plain_b % 16 == 0 /\ length iv_b % 16 == 0 /\ length keys_b % 16 == 0 /\ length cipher_b % 16 == 0
/\ (    let mods = M.loc_buffer cipher_b in 
    B.live h plain_b /\ B.live h iv_b /\ B.live h keys_b /\ B.live h cipher_b /\
    M.loc_disjoint (M.loc_buffer plain_b) mods /\
    M.loc_disjoint (M.loc_buffer keys_b)  mods /\
    
    B.length plain_b  == bytes_to_quad_size num_bytes * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length plain_b % 16 == 0 /\

    4096 * num_bytes < pow2_32 /\
    256 * bytes_to_quad_size num_bytes < pow2_32 /\

    // AES reqs
    B.length keys_b == (nr AES_128 + 1) * 16 /\
    B.length keys_b % 16 == 0 /\  // REVIEW: Should be derivable from line above :(
    keys_match key keys_b h /\

    // Extra reqs
    (let num_bytes = num_bytes in
     let num_blocks = num_bytes / 16 in
     let iv = buffer_to_quad32 iv_b h in
     num_bytes % 16 <> 0 /\
     0 < num_bytes /\ num_bytes < 16 * bytes_to_quad_size num_bytes /\
     16 * (bytes_to_quad_size num_bytes - 1) < num_bytes /\
     gctr_partial AES_128 
                  num_blocks 
                  (buffer_to_seq_quad32 plain_b h) 
                  (buffer_to_seq_quad32  cipher_b h) 
                  (Ghost.reveal key) 
                  (Ghost.reveal iv_old) /\
     iv == inc32 (Ghost.reveal iv_old) num_blocks) 
     )

let post_cond (h:HS.mem) (h':HS.mem) (plain_b:b8) (num_bytes:nat32) (iv_old:Ghost.erased (quad32)) (iv_b:b8) (key:Ghost.erased (aes_key_LE AES_128)) (keys_b:b8) (cipher_b:b8) = length plain_b % 16 == 0 /\ length iv_b % 16 == 0 /\ length keys_b % 16 == 0 /\ length cipher_b % 16 == 0 /\ (let mods = M.loc_buffer cipher_b in
    M.modifies mods h h' /\
    B.live h' plain_b /\ B.live h' iv_b /\ B.live h' keys_b /\ B.live h' cipher_b /\
    
    B.length plain_b  == bytes_to_quad_size num_bytes * 16 /\
    B.length cipher_b == B.length plain_b /\
    B.length iv_b == 16 /\
    B.length plain_b % 16 == 0 /\
    B.length keys_b == (nr AES_128 + 1) * 16 /\

    (let num_bytes = num_bytes in
     let num_blocks = num_bytes / 16 in
     let iv_new = buffer_to_quad32 iv_b h in

     // We modified cipher_b, but we didn't disrupt the work that was previously done
     let cipher_blocks  = Seq.slice (buffer_to_seq_quad32 cipher_b h)  0 num_blocks in
     let cipher_blocks' = Seq.slice (buffer_to_seq_quad32 cipher_b h') 0 num_blocks in
     cipher_blocks == cipher_blocks' /\
     
     // GCTR
     (let plain  = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32  plain_b h))  0 num_bytes in
      let cipher = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 cipher_b h')) 0 num_bytes in     
      cipher == gctr_encrypt_LE (Ghost.reveal iv_old) (make_gctr_plain_LE plain) AES_128 (Ghost.reveal key))
    )
  )


val gctr_bytes_extra_buffer: plain_b:b8 -> num_bytes:UInt32.t -> iv_old:Ghost.erased (quad32) -> iv_b:b8 -> key:Ghost.erased (aes_key_LE AES_128) -> keys_b:b8 -> cipher_b:b8 -> Stack unit
	(requires (fun h -> pre_cond h plain_b (UInt32.v num_bytes) iv_old iv_b key keys_b cipher_b ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 plain_b (UInt32.v num_bytes) iv_old iv_b key keys_b cipher_b ))