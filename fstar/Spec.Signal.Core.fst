module Spec.Signal.Core

open Lib.IntTypes
open Lib.ByteSequence
open Lib.Sequence
open Lib.RawIntTypes
open Spec.Signal.Crypto
open Spec.Signal.Messages


#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


let verify_sig (identity_key:pubkey) (signed_pub_key: pubkey) (signature:lbytes 64) : Tot bool =
  verify identity_key signed_pub_key signature

let sign (priv_key:privkey) (pub_key:pubkey) : Tot (lbytes 64) =
  sign priv_key pub_key


let ratchet
    (root_key:key)                   (* $rk_j$    *)
    (our_ephemeral_priv_key:privkey) (* $x_j$     *)
    (their_ephemeral_pub_key:pubkey) (* $g^{y_j}$ *)
    : Tot (key & key) =              (* output: $rk_{j+1}, ck_{j+1,0}$ *)

  let shared_secret =
    dh our_ephemeral_priv_key their_ephemeral_pub_key in
  let keys = hkdf2 shared_secret root_key label_WhisperRatchet in
  let root_key' = sub keys 0 32 in
  let chain_key = sub keys 32 32 in
  (root_key', chain_key)


let initiate'
    (our_identity_priv_key: privkey) (* $i$   *)
    (our_onetime_priv_key: privkey)  (* $e$   *)
    (their_identity_pub_key: pubkey) (* $g^r$ *)
    (their_signed_pub_key: pubkey)   (* $g^s$ *)
    (their_onetime_pub_key: option pubkey)  (* $g^o$, optional *)
    : Tot (lbytes 32) =                    (* output: $rk_0$ *)

  let dh1 = dh our_identity_priv_key their_signed_pub_key in
  let dh2 = dh our_onetime_priv_key their_identity_pub_key in
  let dh3 = dh our_onetime_priv_key their_signed_pub_key in
  let shared_secret =
    match their_onetime_pub_key with
    | None -> ff @| dh1 @| dh2 @| dh3
    | Some their_onetime_pub_key ->
	   let dh4 = dh our_onetime_priv_key their_onetime_pub_key in
	   ff @| dh1 @| dh2 @| dh3 @| dh4 in
  let res = hkdf1 shared_secret zz label_WhisperText in
  res


let initiate
    (our_identity_priv_key: privkey) (* $i$   *)
    (base_priv_key: privkey)
    (our_onetime_priv_key: privkey)  (* $e$   *)
    (their_identity_pub_key: pubkey) (* $g^r$ *)
    (their_signed_pub_key: pubkey)   (* $g^s$ *)
    (their_onetime_pub_key: option pubkey)  (* $g^o$, optional *)
    : Tot (key & key) =
  let root_key0 = initiate'
    our_identity_priv_key
    base_priv_key
    their_identity_pub_key
    their_signed_pub_key
    their_onetime_pub_key
  in
  ratchet root_key0 our_onetime_priv_key their_signed_pub_key


let respond
  (our_identity_priv_key: privkey) (* $r$ *)
  (our_signed_priv_key: privkey)   (* $s$ *)
  (our_onetime_priv_key: option privkey)  (* $o$, optional *)
  (their_identity_pub_key: pubkey) (* $g^i$ *)
  (their_onetime_pub_key: pubkey)  (* $g^e$ *)
  : Tot (root_key:key) =                    (* output: $rk_0$ *)
  let dh1 = dh our_signed_priv_key their_identity_pub_key in
  let dh2 = dh our_identity_priv_key their_onetime_pub_key in
  let dh3 = dh our_signed_priv_key their_onetime_pub_key in
  let shared_secret =
    match our_onetime_priv_key with
    | None -> ff @| dh1 @| dh2 @| dh3
    | Some our_onetime_priv_key ->
	let dh4 = dh our_onetime_priv_key their_onetime_pub_key in
	ff @| dh1 @| dh2 @| dh3 @| dh4
  in
  hkdf1 shared_secret zz label_WhisperText


let fill_message_keys
    (chain_key:privkey)
    : Tot (privkey & privkey) =
  let msg_key = hmac chain_key one in
  let chain_key' = hmac chain_key two in
  msg_key, chain_key'


let size_encrypt_max_length
  (plen:size_nat{plen + 16 <= max_size_t /\ cipherlen plen + 140 <= max_size_t})
  : size_nat =
  9 + size_mac_whisper_msg_extra_info + plen + 16 (* We add 16 because of the block padding *)

let encrypt_get_length
    (prev_counter:size_nat)
    (counter:size_nat)
    (plen:size_nat{plen + 16 <= max_size_t /\ cipherlen plen + 140  + 64 <= max_size_t})
    : Tot (r:size_nat{r <= size_encrypt_max_length plen}) =
    1 + (serialize_whisper_message_get_length prev_counter counter (cipherlen plen)) + 8


let encrypt
    (our_identity_pub_key:pubkey)    (* $g^i$ or $g^r$ *)
    (their_identity_pub_key:pubkey)  (* $g^r$ or $g^i$ *)
    (msg_key:key)                    (* $ck_j$ *)
    (our_ephemeral_pub_key:pubkey)   (* $g^{x}$ *)
    (prev_counter:size_nat)          (* previous $k$ *)
    (counter:size_nat)               (* current  $j$ *)
    (plaintext:plain_bytes)	     (* message $m_j$ *)
    : Tot (lbytes (encrypt_get_length prev_counter counter (length plaintext))) =
    (* output: $c_j$, $t_j$, $ck_{j+1}$ *)
  let keys = hkdf3 msg_key zz label_WhisperMessageKeys in
  let enc_key = sub keys 0 32 in
  let mac_key = sub keys 32 32 in
  let enc_iv  = sub keys 64 16 in
  let ciphertext = aes_enc enc_key enc_iv plaintext in
  (* FStarEncrypt returns here with (ciphertext & mac_key) *)
  let whisper_msg = serialize_whisper_message our_ephemeral_pub_key
		      prev_counter counter ciphertext in
  (* BB: 2019/11/04 *)
  assume(length whisper_msg + size_mac_whisper_msg_extra_info +
    Spec.Hash.Definitions.block_length (Spec.Hash.Definitions.SHA2_256) < max_size_t);
  let tag8 : lbytes 8 = mac_whisper_msg mac_key their_identity_pub_key our_identity_pub_key whisper_msg in
  let c0 : lbytes 1 = create 1 (((u8 3) <<. (size 4)) |. (u8 3)) in
  let output = concat (concat c0 (to_lseq whisper_msg)) tag8 in
  output


let decrypt
    (our_identity_pub_key:pubkey)    // $g^i$ or $g^r$
    (their_identity_pub_key:pubkey)  // $g^r$ or $g^i$
    (remote_ephemeral_key:pubkey)
    (msg_key:key)                  // $ck_j$
    (prev_counter:size_nat)          // prev msg number $k$
    (counter:size_nat)               // current msg number $j$
    (ciphertext:cipher_bytes)	       // ciphertext $c_j$
    (tag8:lbytes 8)                  // tag $t_j$
    : Tot (option (plain_bytes)) =   // outputs: $m_j$, $ck_{j+1}$

  let len = length ciphertext in
  let ciphertext = to_lseq ciphertext in
  let keys = hkdf3 msg_key zz label_WhisperMessageKeys in
  let enc_key = sub keys 0 32 in
  let mac_key = sub keys 32 32 in
  let enc_iv  = sub keys 64 16 in
  let whisper_message =
    serialize_whisper_message remote_ephemeral_key prev_counter counter ciphertext
  in
  let exp_tag8 =
    mac_whisper_msg mac_key our_identity_pub_key their_identity_pub_key whisper_message in
  if not (equal_bytes tag8 exp_tag8) then
    None
  else
    let plain = aes_dec enc_key enc_iv ciphertext in
    match plain with
    | Some plain -> Some plain
    | None -> None


let generate_key_pair (e: Ghost.erased entropy) : Tot (privkey & pubkey) =
  let priv = random_bytes e 32 in
  (priv, priv_to_pub priv)
