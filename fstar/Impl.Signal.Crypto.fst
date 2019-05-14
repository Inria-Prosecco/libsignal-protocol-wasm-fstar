module Impl.Signal.Crypto

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence

#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 20"

private val const_five1: b:ilbuffer uint8 (size 1){
  recallable b /\ witnessed b Spec.Signal.Crypto.five1
}
private let const_five1 = createL_global Spec.Signal.Crypto.five1_list

/// Type definitions

type privkey_p = lbuffer uint8 (size Spec.Signal.Crypto.size_privkey)
type pubkey_p = lbuffer uint8 (size Spec.Signal.Crypto.size_pubkey)
type key_p = lbuffer uint8 (size Spec.Signal.Crypto.size_key)
type sigval_p = lbuffer uint8 (size Spec.Signal.Crypto.size_sigval)

val secure_compare:
    #vlen: Ghost.erased size_nat
  -> len: size_t{size_v len == Ghost.reveal vlen}
  -> input0: lbuffer uint8 len
  -> input1: lbuffer uint8 len ->
  Stack bool
	 (requires (fun h -> live h input0 /\ live h input1))
	 (ensures (fun h0 b h1 -> modifies0 h0 h1 /\
	   b = Lib.Sequence.for_all2 (fun (x:uint8) (y:uint8) ->
	     Lib.RawIntTypes.(u8_to_UInt8 x = u8_to_UInt8 y
	   )) (as_seq h0 input0) (as_seq h0 input1)
	 ))

let secure_compare #vlen len input0 input1 =
 let res = Lib.ByteBuffer.lbytes_eq #len input0 input1 in
 // This could be fixed by i) adding an interface to that file, then ii)
 // friend'ing Lib.ByteSequence in order to reveal the definition of lbytes_eq,
 // then prove this.
 admit();
 res


val priv_to_pub:
    output: lbuffer uint8 (size 33)
  -> secret: lbuffer uint8 (size 32) ->
  Stack unit
	 (requires (fun h -> live h output /\ live h secret /\ disjoint output secret))
	 (ensures (fun h0 _ h1 -> modifies1 output h0 h1 /\
	   as_seq h1 output == Spec.Signal.Crypto.priv_to_pub (as_seq h0 secret)
	 ))

#reset-options "--z3rlimit 50 --max_ifuel 0 --max_fuel 0"

let priv_to_pub output secret =
  (**) let h0 = ST.get () in
  push_frame ();
  let pub = sub output (size 1) (size 32) in
  let secret' = create (size 32) (u8 0) in
  copy secret' secret;
  upd secret' (size 0) (index secret' (size 0) &. (u8 248));
  upd secret' (size 31) (index secret' (size 31) &. (u8 127));
  upd secret' (size 31) (index secret' (size 31) |. (u8 64));
  (**) let h1 = ST.get () in
  Hacl.Curve25519_51.secret_to_public pub secret';
  (**) let h2 = ST.get () in
  (**) Seq.eq_intro (as_seq h2 pub) (Spec.Curve25519.secret_to_public (as_seq h1 secret'));
  recall_contents const_five1 Spec.Signal.Crypto.five1;
  let pub_tag = sub output (size 0) (size 1) in
  copy pub_tag const_five1;
  assert(disjoint pub_tag pub);
  (**) let h3 = ST.get () in
  (**) Seq.eq_intro (as_seq h2 pub) (as_seq h3 pub);
  (**) Seq.lemma_concat2 1 Spec.Signal.Crypto.five1 32 (as_seq h2 pub) (as_seq h3 output);
  (**) Seq.eq_intro (as_seq h3 output) (Spec.Signal.Crypto.priv_to_pub (as_seq h0 secret));
  pop_frame ()


val dh:
    output: lbuffer uint8 (size 32)
  -> secret: lbuffer uint8 (size 32)
  -> public: lbuffer uint8 (size 33) ->
  Stack unit
	 (requires (fun h -> live h output /\ live h secret /\ live h public /\
	   disjoint output secret /\ disjoint output public))
	 (ensures (fun h0 _ h1 -> modifies1 output h0 h1 /\
	   as_seq h1 output == Spec.Signal.Crypto.dh (as_seq h0 secret) (as_seq h0 public)
	 ))

let dh output secret public =
  let public = sub public (size 1) (size 32) in
  Hacl.Curve25519_51.ecdh output secret public;
  admit()


val hkdf1:
     #vlen: (Ghost.erased size_nat){Ghost.reveal vlen <= 160}
  -> #vilen: (Ghost.erased size_nat){Ghost.reveal vilen <= 32}
  -> output:lbuffer uint8 (size 32)
  -> len  :size_t{v len = Ghost.reveal vlen}
  -> input:lbuffer uint8 len
  -> salt:ilbuffer uint8 (size 32)
  -> ilen  :size_t{v ilen = Ghost.reveal vilen}
  -> info:ilbuffer uint8 ilen  ->
  Stack unit
        (requires (fun h -> live h output /\ live h input /\ live h salt /\ live h info
                         /\ disjoint output input /\ disjoint output salt /\ disjoint output info))
        (ensures  (fun h0 _ h1 -> modifies1 output h0 h1 /\
	  as_seq h1 output == Spec.Signal.Crypto.hkdf1
	    (as_seq h0 input) (as_seq h0 salt) (as_seq h0 info)
	))

let hkdf1 #vlen #vilen output len input salt ilen info =
  push_frame ();
  let tmp = create (size 32) (u8 0) in
  admit();
  // Type mismatch: info is immutable but HKDF wants a mutable buffer. This will
  // be fixed once we convert all of HACL* to the new LowStar.ConstBuffer.
  Hacl.HKDF_SHA2_256.hkdf_extract tmp salt (size 32) input len;
  Hacl.HKDF_SHA2_256.hkdf_expand output tmp (size 32) info ilen (size 32);
  pop_frame ()

val hkdf2:
    #vilen: (Ghost.erased size_nat){Ghost.reveal vilen <= 32}
  -> output: lbuffer uint8 (size 64)
  -> input: lbuffer uint8 (size 32)
  -> salt: lbuffer uint8 (size 32)
  -> ilen: size_t{v ilen = Ghost.reveal vilen}
  -> info: ilbuffer uint8 ilen ->
  Stack unit
        (requires (fun h -> live h output /\ live h input /\ live h salt /\ live h info
                         /\ disjoint output input
                         /\ disjoint output salt
                         /\ disjoint output info))
        (ensures  (fun h0 _ h1 -> modifies1 output h0 h1 /\
	  as_seq h1 output == Spec.Signal.Crypto.hkdf2
	    (as_seq h0 input) (as_seq h0 salt) (as_seq h0 info)
	))

let hkdf2 #vilen output input salt ilen info =
  push_frame ();
  let tmp = create (size 32) (u8 0) in
  admit();
  // Same as above.
  Hacl.HKDF_SHA2_256.hkdf_extract tmp salt (size 32) input (size 32);
  Hacl.HKDF_SHA2_256.hkdf_expand output tmp (size 32) info ilen (size 64);
  pop_frame ()

val hkdf3:
     #vilen: (Ghost.erased size_nat){Ghost.reveal vilen <= 32}
  -> output:lbuffer uint8 (size 96)
  -> input:lbuffer uint8 (size 32)
  -> salt: ilbuffer uint8 (size 32)
  -> ilen:size_t{v ilen = Ghost.reveal vilen}
  -> info: ilbuffer uint8 ilen ->
  Stack unit
        (requires (fun h -> live h output /\ live h input /\ live h salt /\ live h info
                         /\ disjoint output input
                         /\ disjoint output salt
                         /\ disjoint output info))
        (ensures  (fun h0 _ h1 -> modifies1 output h0 h1 /\
	  as_seq h1 output == Spec.Signal.Crypto.hkdf3
	    (as_seq h0 input)  (as_seq h0 salt) (as_seq h0 info)
	))

let hkdf3 #vilen output input salt ilen info =
  push_frame ();
  let tmp = create (size 32) (u8 0) in
  // Same as above.
  admit();
  Hacl.HKDF_SHA2_256.hkdf_extract tmp salt (size 32) input (size 32);
  Hacl.HKDF_SHA2_256.hkdf_expand output tmp (size 32) info ilen (size 96);
  pop_frame ()

val hkdf_standalone:
     #vlen: (Ghost.erased size_nat){Ghost.reveal vlen <= 160}
  -> #vilen: (Ghost.erased size_nat){Ghost.reveal vilen <= 32}
  -> output:lbuffer uint8 (size 96)
  -> len  :size_t{v len = Ghost.reveal vlen}
  -> input:lbuffer uint8 len
  -> slen: size_t
  -> salt:ilbuffer uint8 slen
  -> ilen  :size_t{v ilen = Ghost.reveal vilen}
  -> info:ilbuffer uint8 ilen  ->
  Stack unit
        (requires (fun h -> live h output /\ live h input /\ live h salt /\ live h info
                         /\ disjoint output input /\ disjoint output salt /\ disjoint output info))
        (ensures  (fun h0 _ h1 -> modifies1 output h0 h1))

let hkdf_standalone #vlen #vilen output len input slen salt ilen info =
  push_frame ();
  let tmp = create (size 32) (u8 0) in
  // Missing functional correctness for HKDF. This will be fixed once _dev
  // abandons its unproven HKDF in favor of the one on the fstar-master branch.
  admit();
  Hacl.HKDF_SHA2_256.hkdf_extract tmp salt slen input len;
  Hacl.HKDF_SHA2_256.hkdf_expand output tmp (size 32) info ilen (size 96);
  pop_frame ()


val enc:
     #vlen: (Ghost.erased size_nat){
       Ghost.reveal vlen + 16 <= max_size_t /\
       Ghost.reveal vlen > 0 /\
       Spec.Signal.Crypto.cipherlen (Ghost.reveal vlen) + 140 <= max_size_t
     }
  -> len: size_t{size_v len = Ghost.reveal vlen}
  -> ciphertext: lbuffer uint8 (len +! size 16)
  -> key: lbuffer uint8 (size 32)
  -> iv: lbuffer uint8 (size 16)
  -> plaintext: lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h iv /\ live h plaintext
                     /\ disjoint ciphertext key
                     /\ disjoint ciphertext iv
                     /\ disjoint ciphertext plaintext))
    (ensures  (fun h0 _ h1 -> modifies1 ciphertext h0 h1 /\
      Seq.sub (as_seq h1 ciphertext) 0 (Spec.Signal.Crypto.cipherlen (Ghost.reveal vlen)) ==
	Spec.Signal.Crypto.aes_enc (as_seq h0 key) (as_seq h0 iv) (as_seq h0 plaintext)
    ))

let enc #vlen len ciphertext key iv plaintext =
  assert((Ghost.reveal vlen / 16) * 16 + 16 <= max_size_t);
  let _ = Hacl.Impl.AES_256_CBC.aes256_cbc_encrypt ciphertext key iv plaintext len in
  // Missing functional specification for AES256.
  admit()

val enc_standalone:
     #vplen: (Ghost.erased size_nat){
       Ghost.reveal vplen + 16 <= max_size_t /\
       Ghost.reveal vplen > 0 /\
       Spec.Signal.Crypto.cipherlen (Ghost.reveal vplen) + 140 <= max_size_t
     }
  -> clen: size_t{size_v clen = Ghost.reveal vplen + 16}
  -> ciphertext: lbuffer uint8 clen
  -> key: lbuffer uint8 (size 32)
  -> iv: lbuffer uint8 (size 16)
  -> plen:size_t{size_v plen = Ghost.reveal vplen}
  -> plaintext: lbuffer uint8 plen
  -> Stack size_t
    (requires (fun h -> live h ciphertext /\ live h key /\ live h iv /\ live h plaintext
                     /\ disjoint ciphertext key
                     /\ disjoint ciphertext iv
                     /\ disjoint ciphertext plaintext))
    (ensures  (fun h0 _ h1 -> modifies1 ciphertext h0 h1 /\
      Seq.sub (as_seq h1 ciphertext) 0 (Spec.Signal.Crypto.cipherlen (Ghost.reveal vplen)) ==
	Spec.Signal.Crypto.aes_enc (as_seq h0 key) (as_seq h0 iv) (as_seq h0 plaintext)
    ))

let enc_standalone #vplen clen ciphertext key iv plen plaintext =
  assert((Ghost.reveal vplen / 16) * 16 + 16 <= max_size_t);
  let real_clen = Hacl.Impl.AES_256_CBC.aes256_cbc_encrypt ciphertext key iv plaintext plen in
  // Same as above.
  admit();
  real_clen

val dec:
    #vlen: (Ghost.erased size_nat){
      Ghost.reveal vlen % 16 = 0 /\ Ghost.reveal vlen > 0 /\
      Ghost.reveal vlen + Spec.Signal.Messages.size_whisper_message_extra_info <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vlen) +
        Spec.Signal.Messages.size_mac_whisper_msg_extra_info + 32 <= max_size_t
    }
  -> len: size_t{size_v len = Ghost.reveal vlen}
  -> plaintext: lbuffer uint8 len
  -> key: lbuffer uint8 (size 32)
  -> iv: lbuffer uint8 (size 16)
  -> ciphertext: lbuffer uint8 len ->
  Stack size_t
    (requires (fun h -> live h ciphertext /\ live h key /\ live h iv /\ live h plaintext
                     /\ disjoint plaintext key
                     /\ disjoint plaintext iv
                     /\ disjoint plaintext ciphertext))
    (ensures  (fun h0 plainlen h1 -> modifies1 plaintext h0 h1 /\
      begin if v plainlen <> 0 then
	v plainlen + 16 <= max_size_t /\
	Spec.Signal.Crypto.cipherlen (v plainlen) == Ghost.reveal vlen /\
	Some(Seq.sub (as_seq h1 plaintext) 0 (v plainlen)) == Spec.Signal.Crypto.aes_dec
	  (as_seq h0 key) (as_seq h0 iv) (as_seq h0 ciphertext)
      else
	None == Spec.Signal.Crypto.aes_dec
	  (as_seq h0 key) (as_seq h0 iv) (as_seq h0 ciphertext)
      end
    ))

let dec #vlen len plaintext key iv ciphertext =
  assert((Ghost.reveal vlen / 16) * 16 + 16 <= max_size_t);
  let res =
    Hacl.Impl.AES_256_CBC.aes256_cbc_decrypt plaintext key iv ciphertext len
  in
  // Same as above.
  admit();
  res

val dec_standalone:
    #vlen: (Ghost.erased size_nat){
      Ghost.reveal vlen % 16 = 0 /\ Ghost.reveal vlen > 0 /\
      Ghost.reveal vlen + Spec.Signal.Messages.size_whisper_message_extra_info <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vlen) +
        Spec.Signal.Messages.size_mac_whisper_msg_extra_info + 32 <= max_size_t
    }
  -> len: size_t{size_v len = Ghost.reveal vlen}
  -> plaintext: lbuffer uint8 len
  -> key: lbuffer uint8 (size 32)
  -> iv: lbuffer uint8 (size 16)
  -> clen: size_t{size_v clen = Ghost.reveal vlen}
  -> ciphertext: lbuffer uint8 len ->
  Stack size_t
    (requires (fun h -> live h ciphertext /\ live h key /\ live h iv /\ live h plaintext
                     /\ disjoint plaintext key
                     /\ disjoint plaintext iv
                     /\ disjoint plaintext ciphertext))
    (ensures  (fun h0 plainlen h1 -> modifies1 plaintext h0 h1 /\
      begin if v plainlen <> 0 then
	v plainlen + 16 <= max_size_t /\
	Spec.Signal.Crypto.cipherlen (v plainlen) == Ghost.reveal vlen /\
	Some(Seq.sub (as_seq h1 plaintext) 0 (v plainlen)) == Spec.Signal.Crypto.aes_dec
	  (as_seq h0 key) (as_seq h0 iv) (as_seq h0 ciphertext)
      else
	None == Spec.Signal.Crypto.aes_dec
	  (as_seq h0 key) (as_seq h0 iv) (as_seq h0 ciphertext)
      end
    ))

let dec_standalone #vlen len plaintext key iv clen ciphertext =
  dec #vlen len plaintext key iv ciphertext


val hmac:
     #vdlen: Ghost.erased size_nat
  -> mac: lbuffer uint8 (size 32)
  -> key: lbuffer uint8 (size 32)
  -> dlen: size_t{v dlen = Ghost.reveal vdlen  /\ v dlen +
    Spec.Hash.Definitions.block_length Spec.Hash.Definitions.SHA2_256 < max_size_t }
  -> data: ilbuffer uint8 dlen ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data
                       /\ disjoint mac key
                       /\ disjoint mac data))
        (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1 /\
	  as_seq h1 mac == Spec.Signal.Crypto.hmac (as_seq h0 key) (as_seq h0 data)
	))

let hmac #vdlen mac key dlen data =
  // Type mismatch: data is immutable but HMAC wants a mutable buffer. This will
  // be fixed once we convert all of HACL* to the new LowStar.ConstBuffer.
  admit();
  Hacl.HMAC.compute_sha2_256 mac key (size 32) data dlen

val hmac_standalone:
    #vdlen: Ghost.erased size_nat
  -> mac: lbuffer uint8 (size 32)
  -> keylen: size_t{ v keylen +
    Spec.Hash.Definitions.block_length Spec.Hash.Definitions.SHA2_256 < max_size_t}
  -> key: lbuffer uint8 keylen
  -> dlen: size_t{v dlen = Ghost.reveal vdlen  /\ v dlen +
    Spec.Hash.Definitions.block_length Spec.Hash.Definitions.SHA2_256 < max_size_t }
  -> data: lbuffer uint8 dlen ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data
                       /\ disjoint mac key
                       /\ disjoint mac data))
        (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1))

let hmac_standalone #vdlen mac keylen key dlen data =
  Hacl.HMAC.compute_sha2_256 mac key keylen data dlen

(* Voir dans lib pour caster un immut vers un mut *)
val hmac_mut:
     #vdlen: Ghost.erased size_nat
  -> mac: lbuffer uint8 (size 32)
  -> key: lbuffer uint8 (size 32)
  -> dlen: size_t{v dlen = Ghost.reveal vdlen /\ v dlen +
    Spec.Hash.Definitions.block_length Spec.Hash.Definitions.SHA2_256 < max_size_t
  }
  -> data: lbuffer uint8 dlen ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data
                       /\ disjoint mac key
                       /\ disjoint mac data))
        (ensures  (fun h0 _ h1 -> modifies1 mac h0 h1 /\
	  as_seq h1 mac == Spec.Signal.Crypto.hmac (as_seq h0 key) (as_seq h0 data)
	))

let hmac_mut #vdlen mac key dlen data =
 Hacl.HMAC.compute_sha2_256 mac key (size 32) data dlen;
 admit()

val curve25519_sign_modified_:
  signature:lbuffer uint8 (size 64) ->
  secret:lbuffer uint8 (size 64) ->
  len:size_t{v len + 64 <= max_size_t} ->
  msg:lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\
      disjoint signature secret /\ disjoint signature msg
    ))
    (ensures (fun h0 _ h1 -> modifies1 signature h0 h1))

#set-options "--z3rlimit 100"

let curve25519_sign_modified_ signature secret len msg =
  push_frame();
  let sk = sub secret (size 0) (size 32) in
  let pk = sub secret (size 32) (size 32) in
  let scratch = create (size 25) (u64 0) in
  let r = sub scratch (size 0) (size 5) in
  let h = sub scratch (size 5) (size 5) in
  let rb = create (size 32) (u8 0) in
  let aq = sub scratch (size 10) (size 5) in
  let ha = sub scratch (size 15) (size 5) in
  let s = sub scratch (size 20) (size 5)in
  let rs' = sub signature (size 0) (size 32) in
  let s' = sub signature (size 32) (size 32) in
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre r sk len msg;
  Hacl.Impl.Store56.store_56 rb r;
  Hacl.Impl.Ed25519.Sign.Steps.point_mul_g_compress rs' rb;
  Hacl.Impl.SHA512.ModQ.sha512_modq_pre_pre2 h rs' pk len msg;
  Hacl.Impl.Load56.load_32_bytes aq sk;
  Hacl.Impl.BignumQ.Mul.mul_modq ha h aq;
  Hacl.Impl.BignumQ.Mul.add_modq s r ha;
  Hacl.Impl.Store56.store_56 s' s;
  pop_frame()

#set-options "--z3rlimit 20"

val curve25519_sign_modified:
  signature:lbuffer uint8 (size 64) ->
  secret:lbuffer uint8 (size 32) ->
  len:size_t{v len + 64 <= max_size_t} ->
  msg:lbuffer uint8 len ->
  Stack unit
    (requires (fun h -> live h signature /\ live h msg /\ live h secret /\
      disjoint signature secret /\ disjoint signature msg
    ))
    (ensures (fun h0 _ h1 -> modifies1 signature h0 h1))

let curve25519_sign_modified signature secret len msg =
  push_frame ();
  let ed_key = create (size 64) (u8 0) in
  update_sub ed_key (size 0) (size 32) secret;
  //blit secret 0ul ed_key 0ul 32ul;
  let ed_pub = sub ed_key (size 32) (size 32) in
  Hacl.Impl.Ed25519.Sign.Steps.point_mul_g_compress ed_pub secret;
  let sign_bit = FStar.UInt8.(ed_key.(size 63) &. (u8 0x80)) in
  curve25519_sign_modified_ signature ed_key len msg;
  signature.(size 63) <- FStar.UInt8.(signature.(size 63) |. sign_bit);
  pop_frame()

val sign:
    #vlen:(Ghost.erased size_nat){8 * Ghost.reveal vlen < max_size_t}
  -> sigval: lbuffer uint8 (size 64)
  -> secret: privkey_p
  -> len:size_t{v len = Ghost.reveal vlen}
  -> msg:lbuffer uint8 len ->
  Stack unit
	 (requires (fun h -> live h sigval /\ live h secret /\ live h msg
					      /\ disjoint sigval secret
					      /\ disjoint sigval msg))
	 (ensures (fun h0 _ h1 -> modifies1 sigval h0 h1 /\
	   as_seq h1 sigval == Spec.Signal.Crypto.sign (as_seq h0 secret) (as_seq h0 msg)
	 ))

let sign #vlen sigval secret len msg =
  curve25519_sign_modified sigval secret len msg;
  admit()

val curve25519_verify:
  public:lbuffer uint8 (size 32) ->
  len:size_t{v len + 64 <= max_size_t} ->
  msg:lbuffer uint8 len ->
  signature:lbuffer uint8 (size 64) ->
  Stack bool
    (requires (fun h -> live h signature /\ live h msg /\ live h public))
    (ensures (fun h0 _ h1 -> modifies0 h0 h1))

#set-options "--z3rlimit 100"

let curve25519_verify public len msg signature =
  (**) let h0 = ST.get () in
  push_frame ();
  (**) let h1 = ST.get () in
  let scratch = create (size 30) (u64 0) in
  let x = sub scratch (size 0) (size 5) in
  let xp1 = sub scratch (size 5) (size 5) in
  let xm1 = sub scratch (size 10) (size 5)in
  let xinv = sub scratch (size 15) (size 5) in
  let one = sub scratch (size 20) (size 5) in
  let ed_y = sub scratch (size 25) (size 5) in
  let edpub = create (size 32) (u8 0) in
  let signature_copy = create (size 64) (u8 0) in
  copy signature_copy signature;
  one.(size 0) <- u64 1;
  Hacl.Bignum25519.load_51 x public;
  copy xm1 one;
  //Buffer.blit one 0ul xm1 0ul 5ul;
  Hacl.Bignum25519.fdifference xm1 x;
  copy xp1 x;
  //Buffer.blit x 0ul xp1 0ul 5ul;
  Hacl.Bignum25519.fsum xp1 one;
  Hacl.Bignum25519.inverse xinv xp1;
  Hacl.Bignum25519.fmul ed_y xm1 xinv;
  Hacl.Bignum25519.store_51 edpub ed_y;
  let old_top = signature_copy.(size 63) in
  edpub.(size 31) <- edpub.(size 31) |. (old_top &. (u8 0x80));
  signature_copy.(size 63) <- old_top &. (u8 0x7F);
  let b = Hacl.Impl.Ed25519.Verify.verify edpub len msg signature_copy in
  (**) let h2 = ST.get () in
  pop_frame();
  (**) let h3 = ST.get () in
  (**) LowStar.Monotonic.Buffer.(modifies_fresh_frame_popped h0 h1 loc_none h2 h3);
  b

(*_dev_wasm *)
val verify:
    #vlen: (Ghost.erased size_nat){8 * Ghost.reveal vlen < max_size_t}
  -> sigval: lbuffer uint8 (size 64)
  -> pub: pubkey_p
  -> len:size_t{size_v len = Ghost.reveal vlen}
  -> msg: lbuffer uint8 len->
  Stack bool
    (requires (fun h -> live h sigval /\ live h pub /\ live h msg))
    (ensures (fun h0 b h1 -> modifies0 h0 h1 /\
       b == Spec.Signal.Crypto.verify
	 (as_seq h0 pub) (as_seq h0 msg) (as_seq h0 sigval)
    ))

#reset-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 20"

let verify #vlen sigval pub len msg =
  let public = sub pub (size 1) (size 32) in
  let res = curve25519_verify public len msg sigval in
  admit();
  res

let cipherlen (plen:size_t{v plen + 16 <= max_size_t})
  : Tot (r:size_t{v r = Spec.Signal.Crypto.cipherlen (v plen)}) =
  ((plen +. size 16) /. size 16) *. size 16

val ecdhe:
    shared:lbuffer uint8 32ul
  -> my_priv:lbuffer uint8 32ul
  -> their_pub:lbuffer uint8 32ul
  -> Stack unit
    (requires fun h0 ->
      live h0 shared /\ live h0 my_priv /\ live h0 their_pub /\
      disjoint shared my_priv /\ disjoint shared their_pub)
    (ensures  fun h0 _ h1 -> modifies (loc shared) h0 h1 /\
      as_seq h1 shared == Spec.Curve25519.scalarmult (as_seq h0 my_priv) (as_seq h0 their_pub))
let ecdhe shared my_priv their_pub =
  Hacl.Curve25519_51.ecdh shared my_priv their_pub

assume val random_bytes: e:(Ghost.erased Spec.Signal.Crypto.entropy) ->
  len:size_t -> output:lbuffer uint8 len -> Stack unit
  (requires (fun h -> live h output)) (ensures (fun h0 _  h1 -> modifies1 output h0 h1 /\
    as_seq h1 output == Spec.Signal.Crypto.random_bytes e (v len)
  ))

val hash_sha512:
  dst:lbuffer uint8 64ul ->
  input_len:size_t ->
  input:lbuffer uint8 input_len ->
  HyperStack.ST.Stack unit
    (requires (fun h ->
      live h input /\
      live h dst /\
      disjoint input dst /\
      length input < Spec.Hash.Definitions.max_input_length Spec.Hash.Definitions.SHA2_512))
    (ensures (fun h0 _ h1 ->
      modifies1 dst h0 h1 /\
      as_seq h1 dst ==
      Spec.Hash.hash Spec.Hash.Definitions.SHA2_512 (as_seq h0 input)))

let hash_sha512 dst input_len input =
  Hacl.Hash.SHA2.hash_512 input input_len dst
