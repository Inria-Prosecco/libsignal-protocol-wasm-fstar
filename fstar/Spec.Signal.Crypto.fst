module Spec.Signal.Crypto

open FStar.Mul
open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(* BB. Relocate to Spec.Signal.Constants ? *)
inline_for_extraction let size_privkey = 32
inline_for_extraction let size_pubkey = 33
inline_for_extraction let size_key = 32
inline_for_extraction let size_iv = 16
inline_for_extraction let size_tag = 32
inline_for_extraction let size_sigval = 64
let cipherlen (plen:size_nat{plen + 16 <= max_size_t}) : size_nat =
  ((plen + 16) / 16) `op_Multiply` 16

type privkey = lbytes size_privkey
type pubkey = lbytes size_pubkey
type key = lbytes size_key
type iv = lbytes size_iv
type tag = lbytes size_tag
type sigval = lbytes size_sigval

(* BB. Relocate to Spec.Signal.Constants ? *)
let pow2_61 : l:unit{pow2 61 == 2305843009213693952} = assert_norm(pow2 61 == 2305843009213693952)

(* BB. Relocate to Spec.Signal.Constants ? *)

let lbytes_sub (x:size_nat) = b:bytes{length b <= x}

inline_for_extraction let five1_list: l:list uint8{List.Tot.length l == 1} =
  [@ inline_let]
  let l = [(u8 0x05)] in
  assert_norm(List.Tot.length l ==1);
  l
inline_for_extraction noextract let five1 : lseq uint8 1 = createL five1_list


val priv_to_pub: our_priv_key:privkey -> our_pub_key:pubkey
let priv_to_pub kpriv =
  let kpriv = upd kpriv 0 (index kpriv 0 &. (u8 248)) in
  let kpriv = upd kpriv 31 (index kpriv 31 &. (u8 127)) in
  let kpriv = upd kpriv 31 (index kpriv 31 |. (u8 64)) in
  let raw_pub_key : lbytes 32 = Spec.Curve25519.secret_to_public kpriv in
  concat five1 raw_pub_key

val dh: our_priv_key:privkey -> their_pub_key:pubkey -> shared_secret:key
let dh kpriv kpub =
  let raw_kpub = sub kpub 1 32 in
  Spec.Curve25519.scalarmult kpriv raw_kpub


val hkdf1: key:lbytes_sub 160 -> salt:lbytes 32 -> info:lbytes_sub 32  -> Tot (lbytes 32)
let hkdf1 key salt info =
  let extracted = Spec.HKDF.hkdf_extract Spec.Hash.Definitions.SHA2_256 salt key in
  Spec.HKDF.hkdf_expand Spec.Hash.Definitions.SHA2_256 extracted info 32

val hkdf2: key:lbytes 32 -> salt:lbytes 32 -> info:lbytes_sub 32 -> lbytes 64
let hkdf2 key salt info =
  let extracted = Spec.HKDF.hkdf_extract Spec.Hash.Definitions.SHA2_256 salt key in
  Spec.HKDF.hkdf_expand Spec.Hash.Definitions.SHA2_256 extracted info 64

val hkdf3: key:lbytes 32 -> salt:lbytes 32 -> info:lbytes_sub 32 -> lbytes 96
let hkdf3 key salt info =
  let extracted = Spec.HKDF.hkdf_extract Spec.Hash.Definitions.SHA2_256 salt key in
  Spec.HKDF.hkdf_expand Spec.Hash.Definitions.SHA2_256 extracted info 96

val aes_enc:
  ek:key ->
  iv:iv ->
  plain:bytes{length plain + Spec.AES256.blocklen <= max_size_t}  ->
  Tot (cipher:bytes{length cipher <= length plain + 16})
let aes_enc ek iv plain =
   Spec.AES256_CBC.aes256_cbc_encrypt ek iv plain (length plain)


val aes_dec:
  ek:key ->
  iv:iv ->
  cipher:bytes{
    length cipher % 16 == 0 /\ length cipher > 0 /\
    length cipher <= max_size_t
  } ->
  Tot (option (plain:bytes{
    length plain + 16 <= max_size_t /\
    cipherlen (length plain) = length cipher
  }))
let aes_dec ek iv cipher =
  Spec.AES256_CBC.aes256_cbc_decrypt ek iv cipher (length cipher)

val hmac:
    key:key
    -> input: bytes{length input +
      Spec.Hash.Definitions.block_length Spec.Hash.Definitions.SHA2_256 < max_size_t} ->
  Tot (lbytes 32)
let hmac mk plain =
  assert_norm(max_size_t <= pow2 61 - 1 - size_key - 64);
  Spec.HMAC.hmac Spec.Hash.Definitions.SHA2_256 mk plain


val sign: sk:privkey -> plain:bytes{8 * length plain < max_size_t} -> sv:sigval
let sign sk plain =
  let len = length plain in
  let ed_key = concat #uint8 #32 #32 sk 
    (Spec.Ed25519.point_compress (Spec.Ed25519.point_mul sk Spec.Ed25519.g)) in
  let sign_bit = index ed_key 63 &. u8 0x80 in
  let sk = sub ed_key 0 32 in
  let pk = sub ed_key 32 32 in
  let r = Spec.Ed25519.sha512_modq (32 + len) (concat #uint8 #32 #len sk plain) in
  let r' = Spec.Ed25519.point_mul (nat_to_bytes_le 32 r) Spec.Ed25519.g in
  let rs = Spec.Ed25519.point_compress r' in
  let h = Spec.Ed25519.sha512_modq (64 + len) (concat #uint8 #64 #len (concat #uint8 #32 #32 rs pk) plain) in
  let s = (r + (h * nat_from_bytes_le sk) % Spec.Ed25519.q) % Spec.Ed25519.q in
  let sig = concat #uint8 #32 #32 rs (nat_to_bytes_le 32 s) in
  upd sig 63 (index sig 63 |. sign_bit)

val verify: pk:pubkey -> plain:bytes{8 * length plain < max_size_t} -> sv:sigval -> bool
let verify pk plain sv =
  let raw_pk = sub pk 1 32 in
  let x = nat_from_bytes_le raw_pk % Spec.Curve25519.prime in
  let xm1 = Spec.Curve25519.fsub Spec.Curve25519.one x in
  let xp1 = Spec.Curve25519.fadd Spec.Curve25519.one x in
  let xinv = Spec.Ed25519.modp_inv xp1 in
  let ed_y = Spec.Curve25519.fmul xm1 xinv in
  let ed_pub = nat_to_bytes_le #SEC 32 ed_y in
  let old_top = index sv 63 in
  let ed_pub = upd #uint8 #32 ed_pub 31 (index #uint8 #32 ed_pub 31 |. (old_top &. u8 0x80)) in
  let sv = upd sv 63 (old_top &. u8 0x7F) in
  Spec.Ed25519.verify ed_pub plain sv

assume type entropy

assume val random_bytes: Ghost.erased entropy -> len:size_nat -> Tot (lbytes len)
