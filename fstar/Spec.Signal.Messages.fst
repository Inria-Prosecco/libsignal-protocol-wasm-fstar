module Spec.Signal.Messages

open FStar.Mul
open Lib.IntTypes
open Lib.RawIntTypes
open Lib.ByteSequence
open Lib.Sequence

open Spec.Signal.Crypto

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 15"

/// Protocol Buffer Serialization

let ( @< ) (#len1:size_nat) (#len2:size_nat{len1+len2 <= max_size_t}) (a:lbytes_sub len1) (b:lbytes_sub len2) : lbytes_sub (len1+len2)  =
  concat (to_lseq a) (to_lseq b)

let ( @: ) (#len:size_nat{len < max_size_t}) (a:uint8) (b:lbytes_sub len) : lbytes_sub (len+1)  =
  let b1 : lbytes_sub 1 = create 1 a in
  ( @< ) #1 #len b1 b


let equal_bytes (#len:size_nat) (b1:lbytes len) (b2:lbytes len) =
  for_all2 (fun (x:uint8) (y:uint8) ->
    Lib.RawIntTypes.(u8_to_UInt8 x = u8_to_UInt8 y)) b1 b2


val serialize_size_get_length: s:size_nat -> Tot (l:size_nat{l <= 5})
let serialize_size_get_length s =
  let size128 : size_nat =  128 in
  let size16384 : size_nat = 16384 in
  let size2097152 : size_nat = 2097152 in
  let size268435456 : size_nat =  268435456 in
  if s < size128 then 1 else
  if s < size16384 then 2 else
  if s < size2097152 then 3 else
  if s < size268435456 then 4
  else 5


let serialize_size (s:size_nat) : lbytes_sub 5 =
  let sz = size s in
  if sz <=. 0x7ful then
    let out = create 1 (u8 0) in
    upd out 0 (to_u8 sz &. u8 0x7f)
  else if sz <=. 0x3ffful then
    let out = create 2 (u8 0) in
    let out = upd out 0 (to_u8 (sz &. 0x7ful) |. u8 0x80) in
    upd out 1 (to_u8 (sz >>. 7ul) &. u8 0x7f)
  else if sz <=. 0x1ffffful then
    let out = create 3 (u8 0) in
    let out = upd out 0 (to_u8 (sz &. 0x7ful) |. u8 0x80) in
    let out = upd out 1 (to_u8 (sz >>. 7ul) |.  u8 0x80) in
    upd out 2 (to_u8 (sz >>. 14ul) &. u8 0x7f)
  else if sz <=. 0xffffffful then
    let out = create 4 (u8 0) in
    let out = upd out 0 (to_u8 (sz &. 0x7ful) |. u8 0x80) in
    let out = upd out 1 (to_u8 (sz >>. 7ul) |. u8 0x80) in
    let out = upd out 2 (to_u8 (sz >>. 14ul) |. u8 0x80) in
    upd out 3 (to_u8 (sz >>. 21ul)  &. u8 0x7f)
  else
    let out = create 5 (u8 0) in
    let out = upd out 0 (to_u8 (sz &. 0x7ful) |. u8 0x80) in
    let out = upd out 1 (to_u8 (sz >>. 7ul) |. u8 0x80) in
    let out = upd out 2 (to_u8 (sz >>. 14ul) |. u8 0x80) in
    let out = upd out 3 (to_u8 (sz >>. 21ul) |. u8 0x80) in
    upd out 4 (to_u8 (sz >>. 28ul) &. u8 0x7f)

let serialize_varint (s:size_nat) (f:uint8) :  lbytes_sub 6 =
  (f <<. (size 3)) @: (serialize_size s)

let serialize_bytes_get_length (b:size_nat{b + 6 <= max_size_t}) : Tot (l:size_nat{l <= b + 6}) =
  1 + serialize_size_get_length b +  b

let serialize_bytes (b:bytes{length b + 6 <= max_size_t}) (f:uint8) : Tot (lbytes_sub (length b + 6)) =
  let b:lbytes_sub (length b) = b in
  ((f <<. (size 3)) |. (u8 2)) @:
    (( @< ) #(serialize_size_get_length (length b)) #(length b) (serialize_size (length b)) b)


/// Signal Constants

inline_for_extraction let zz_list : l:list uint8{List.Tot.length l == 32} =
  [@ inline_let]
  let l = [
    u8 0x00; u8 0x00; u8 0x00; u8 0x00;
    u8 0x00; u8 0x00; u8 0x00; u8 0x00;
    u8 0x00; u8 0x00; u8 0x00; u8 0x00;
    u8 0x00; u8 0x00; u8 0x00; u8 0x00;
    u8 0x00; u8 0x00; u8 0x00; u8 0x00;
    u8 0x00; u8 0x00; u8 0x00; u8 0x00;
    u8 0x00; u8 0x00; u8 0x00; u8 0x00;
    u8 0x00; u8 0x00; u8 0x00; u8 0x00 ]
  in
  assert_norm(List.Tot.length l == 32);
  l

inline_for_extraction noextract let zz : lseq uint8 32 = of_list zz_list


inline_for_extraction let ff_list : l:list uint8{List.Tot.length l == 32} =
  [@ inline_let]
  let l = [
    u8 0xFF; u8 0xFF; u8 0xFF; u8 0xFF;
    u8 0xFF; u8 0xFF; u8 0xFF; u8 0xFF;
    u8 0xFF; u8 0xFF; u8 0xFF; u8 0xFF;
    u8 0xFF; u8 0xFF; u8 0xFF; u8 0xFF;
    u8 0xFF; u8 0xFF; u8 0xFF; u8 0xFF;
    u8 0xFF; u8 0xFF; u8 0xFF; u8 0xFF;
    u8 0xFF; u8 0xFF; u8 0xFF; u8 0xFF;
    u8 0xFF; u8 0xFF; u8 0xFF; u8 0xFF ]
  in
  assert_norm(List.Tot.length l == 32);
  l

inline_for_extraction noextract let ff : lseq uint8 32 = createL ff_list

inline_for_extraction let ff1_list: l:list uint8{List.Tot.length l == 1} =
  [@ inline_let]
  let l = [(u8 0xFF)] in
  assert_norm(List.Tot.length l ==1);
  l
inline_for_extraction noextract let ff1 : lseq uint8 1 = createL ff1_list

inline_for_extraction let fifty_one_list: l:list uint8{List.Tot.length l == 1} =
  [@inline_let]
  let l = [(u8 51)] in
  assert_norm(List.Tot.length l == 1);
  l
inline_for_extraction noextract let fifty_one : lseq uint8 1 = createL fifty_one_list

#set-options "--initial_fuel 1 --max_fuel 1"

let lemma_fifty_one () : Lemma (ensures (
 let const : uint8 = ((u8 3) <<. 4ul) |. (u8 3) in
 fifty_one == create #uint8 1 const
)) =
  let const : uint8 = ((u8 3) <<. 4ul) |. (u8 3) in
  let x = (u8 3) <<. 4ul in
  assert(v x = 48);
  let y = x |. (u8 3) in
  assert_norm(FStar.UInt8.logor 48uy 3uy == 51uy);
  admit();
  assert_norm(y == u8_from_UInt8 (FStar.UInt8.logor 48uy 3uy));
  assert(v const = 51)

inline_for_extraction let zero_list: l:list uint8{List.Tot.length l == 1} =
  [@ inline_let]
  let l = [(u8 0)] in
  assert_norm(List.Tot.length l == 1);
  l
inline_for_extraction noextract let zero : lseq uint8 1 = createL zero_list

inline_for_extraction let one_list: l:list uint8{List.Tot.length l == 1} =
  [@ inline_let]
  let l = [(u8 1)] in
  assert_norm(List.Tot.length l == 1);
  l
inline_for_extraction noextract let one : lseq uint8 1 = createL one_list

inline_for_extraction let two_list: l:list uint8{List.Tot.length l == 1} =
  [@ inline_let]
  let l = [(u8 2)] in
  assert_norm(List.Tot.length l == 1);
  l
inline_for_extraction noextract let two : lseq uint8 1 = createL two_list


inline_for_extraction let vsize_label_WhisperMessageKeys : size_nat = 18
inline_for_extraction val label_WhisperMessageKeys_list: l:list uint8{List.Tot.length l == vsize_label_WhisperMessageKeys}
inline_for_extraction let label_WhisperMessageKeys_list =
  [@inline_let]
  let l = [u8 0x57; u8 0x68; u8 0x69; u8 0x73; u8 0x70; u8 0x65; u8 0x72; u8 0x4d; u8 0x65; u8 0x73; u8 0x73; u8 0x61; u8 0x67; u8 0x65; u8 0x4b; u8 0x65; u8 0x79; u8 0x73] in
  assert_norm(List.Tot.Base.length l == vsize_label_WhisperMessageKeys);
  l

inline_for_extraction noextract val label_WhisperMessageKeys: lseq uint8 vsize_label_WhisperMessageKeys
inline_for_extraction noextract let label_WhisperMessageKeys = createL label_WhisperMessageKeys_list


inline_for_extraction let vsize_label_WhisperText : size_nat = 11
inline_for_extraction val label_WhisperText_list: l:list uint8{List.Tot.length l == vsize_label_WhisperText}
inline_for_extraction let label_WhisperText_list =
  [@inline_let]
  let l  = [u8 0x57; u8 0x68; u8 0x69; u8 0x73; u8 0x70; u8 0x65; u8 0x72; u8 0x54; u8 0x65; u8 0x78; u8 0x74] in
  assert_norm(List.Tot.Base.length l == vsize_label_WhisperText);
  l

inline_for_extraction noextract val label_WhisperText: l:lseq uint8 vsize_label_WhisperText
inline_for_extraction noextract let label_WhisperText = createL label_WhisperText_list


inline_for_extraction let vsize_label_WhisperRatchet : size_nat = 14
inline_for_extraction val label_WhisperRatchet_list: l:list uint8{List.Tot.length l == vsize_label_WhisperRatchet}
inline_for_extraction let label_WhisperRatchet_list =
  [@inline_let]
  let l = [u8 0x57; u8 0x68; u8 0x69; u8 0x73; u8 0x70; u8 0x65; u8 0x72; u8 0x52; u8 0x61; u8 0x74; u8 0x63; u8 0x68; u8 0x65; u8 0x74] in
  assert_norm(List.Tot.Base.length l == vsize_label_WhisperRatchet);
  l

inline_for_extraction noextract val label_WhisperRatchet: lseq uint8 vsize_label_WhisperRatchet
inline_for_extraction noextract let label_WhisperRatchet = createL label_WhisperRatchet_list



/// Signal WhisperMessage Formatting and MAC

let plain_bytes = b:bytes{length b + 16 <= max_size_t /\ cipherlen (length b) + 140 + 64 <= max_size_t}
let cipher_bytes = b:bytes{length b + 140 + 64 <= max_size_t /\ length b > 0 /\ length b % 16 == 0}

let size_whisper_message_extra_info : size_nat = 39 + 6 + 6 + 6

let serialize_whisper_message_get_length
  (prev_counter:size_nat)
  (counter:size_nat)
  (ciphertext:size_nat{ciphertext + size_whisper_message_extra_info <= max_size_t})
  : Tot (r:size_nat{r + 1 <= max_size_t})
  =
  serialize_bytes_get_length size_pubkey +
  1 + serialize_size_get_length counter +
  1 + serialize_size_get_length prev_counter +
  serialize_bytes_get_length ciphertext

let max_whisper_message_len (ciphertext_len:size_nat{
    ciphertext_len + size_whisper_message_extra_info <= max_size_t
  }) : size_nat =
  ciphertext_len + size_whisper_message_extra_info

let serialize_whisper_message
  (our_ephemeral_pub_key:pubkey)
  (prev_counter:size_nat)
  (counter:size_nat)
  (ciphertext:bytes{length ciphertext + size_whisper_message_extra_info <= max_size_t})
  : Tot (lbytes (serialize_whisper_message_get_length
    prev_counter
    counter
    (length ciphertext)
  )) =
  let x0 = serialize_bytes our_ephemeral_pub_key (u8 1) in
  let x1 = serialize_varint counter (u8 2) in
  let x2 = serialize_varint prev_counter (u8 3) in
  let x3 = serialize_bytes ciphertext (u8 4) in
  x0 @< x1 @< x2 @< x3

let size_mac_whisper_msg_extra_info : size_nat = 33 + 33 + 1

let mac_whisper_msg
  (mac_key: key)
  (send_identity_pub_key:pubkey)
  (recv_identity_pub_key:pubkey)
  (whisper_msg:bytes{length whisper_msg + size_mac_whisper_msg_extra_info +
    Spec.Hash.Definitions.block_length (Spec.Hash.Definitions.SHA2_256) < max_size_t
  })
  : Tot (lbytes 8) =
  let mac_input = recv_identity_pub_key @| send_identity_pub_key @| fifty_one @| (to_lseq whisper_msg) in
  let tag = hmac mac_key mac_input in
  let tag8 = sub tag 0 8 in
  tag8
