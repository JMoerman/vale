module GHash_extra

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
open Words.Seq_s
open Types_i
open Types_s
open X64.Machine_s
open X64.Memory_i_s
open X64.Vale.State_i
open X64.Vale.Decls_i
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

let buffer_to_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 /\ B.length b > 0 }) (h:HS.mem) : GTot quad32 =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  assert (B.length b >= 16);
  assert (BV.length b128 > 0);
  BV.sel h b128 0

let buffer_to_seq_quad32 (b:B.buffer UInt8.t { B.length b % 16 == 0 }) (h:HS.mem) : GTot (s:Seq.seq quad32 {Seq.length s == B.length b / 16} ) =
  let b128 = BV.mk_buffer_view b Views.view128 in
  BV.as_buffer_mk_buffer_view b Views.view128;
  BV.get_view_mk_buffer_view b Views.view128;
  BV.length_eq b128;
  (BV.as_seq h b128)

open FStar.Mul

// TODO: Complete with your pre- and post-conditions
let pre_cond (h:HS.mem) (in_b:b8) (hash_b:b8) (h_b:b8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32)) = live h in_b /\ live h hash_b /\ live h h_b /\ locs_disjoint [in_b;hash_b;h_b] /\ length in_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length h_b % 16 == 0 /\
   ( let mods = M.loc_buffer hash_b in 
    B.live h in_b /\ B.live h hash_b /\ B.live h h_b /\ 
    M.loc_disjoint (M.loc_buffer in_b) mods /\
    M.loc_disjoint (M.loc_buffer h_b)  mods /\
    
    B.length in_b  == bytes_to_quad_size num_bytes * 16 /\
    B.length in_b % 16 == 0 /\

    B.length h_b == 16 /\
    B.length hash_b == 16 /\

    4096 * num_bytes < pow2_32 /\
    256 * bytes_to_quad_size num_bytes < pow2_32 /\
    
    (let num_blocks = num_bytes / 16 in    
     let old_hash = buffer_to_quad32 hash_b h in
     //let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     // GHash reqs
     let input = Seq.slice (buffer_to_seq_quad32 in_b h) 0 num_blocks in
     old_hash == ghash_incremental0 h_val (Ghost.reveal orig_hash) input /\
     
     // Extra reqs
     num_bytes % 16 <> 0 /\ 
     0 < num_bytes /\ num_bytes < 16 * bytes_to_quad_size num_bytes /\
     16 * (bytes_to_quad_size num_bytes - 1) < num_bytes /\

     True
    )
)

let post_cond (h:HS.mem) (h':HS.mem) (in_b:b8) (hash_b:b8) (h_b:b8) (num_bytes:nat64) (orig_hash:Ghost.erased (quad32)) = length in_b % 16 == 0 /\ length hash_b % 16 == 0 /\ length h_b % 16 == 0 /\
    B.length in_b  == bytes_to_quad_size num_bytes * 16 /\
    B.length h_b == 16 /\
    B.length hash_b == 16 /\
    (let mods = M.loc_buffer hash_b in
    M.modifies mods h h' /\
    B.live h in_b /\ B.live h hash_b /\ B.live h h_b /\
    (let num_blocks = num_bytes / 16 in
     let old_hash = buffer_to_quad32 hash_b h in
     let new_hash = buffer_to_quad32 hash_b h' in
     let h_val = buffer_to_quad32 h_b h in

     let input_bytes = Seq.slice (le_seq_quad32_to_bytes (buffer_to_seq_quad32 in_b h')) 0 num_bytes in
     let padded_bytes = pad_to_128_bits input_bytes in
     let input_quads = le_bytes_to_seq_quad32 padded_bytes in
     (num_bytes > 0 ==> Seq.length input_quads > 0 /\ 
                       new_hash == ghash_incremental h_val (Ghost.reveal orig_hash) input_quads)
    )
  ) 

val ghash_incremental_extra_stdcall: in_b:b8 -> hash_b:b8 -> h_b:b8 -> num_bytes:UInt64.t -> orig_hash:Ghost.erased (quad32) -> Stack unit
	(requires (fun h -> pre_cond h in_b hash_b h_b (UInt64.v num_bytes) orig_hash ))
	(ensures (fun h0 _ h1 -> post_cond h0 h1 in_b hash_b h_b (UInt64.v num_bytes) orig_hash ))
