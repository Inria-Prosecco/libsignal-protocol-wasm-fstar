module Impl.Signal.Core

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Impl.Signal.Crypto
open Impl.Signal.Messages

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence


#set-options "--z3rlimit 20 --fuel 0 --ifuel 0"

let op_String_Access (#a:Type) (#len:size_t) (h:mem) (b:lbuffer a len) = as_seq h b


val verify_sig:
     identity_pub_key: pubkey_p
  -> signed_pub_key: pubkey_p
  -> signature: lbuffer uint8 (size 64)
  -> Stack bool
  (requires (fun h -> live h identity_pub_key /\ live h signed_pub_key /\ live h signature))
  (ensures (fun h0 b h1 -> modifies0 h0 h1 /\
    b == Spec.Signal.Core.verify_sig h0.[identity_pub_key] h0.[signed_pub_key] h0.[signature]
  ))

let verify_sig identity_pub_key signed_pub_key signature =
  verify #(Ghost.hide 33) signature identity_pub_key (size 33) signed_pub_key


val sign:
     signature: lbuffer uint8 (size 64)
  -> priv_key:privkey_p
  -> pub_key:pubkey_p
  -> Stack unit
    (requires (fun h -> live h signature /\ live h priv_key /\ live h pub_key /\
      disjoint signature priv_key /\ disjoint signature pub_key
    ))
    (ensures (fun h0 _ h1 -> modifies1 signature h0 h1 /\
      h1.[signature] == Spec.Signal.Core.sign h0.[priv_key] h0.[pub_key]
    ))

let sign signature priv_key pub_key =
  sign #(Ghost.hide 33) signature priv_key (size 33) pub_key


val ratchet:
    new_root_key:privkey_p
 -> new_chain_key:privkey_p
 -> root_key: privkey_p
 -> our_ephemeral_priv_key:privkey_p
 -> their_ephemeral_pub_key:pubkey_p
 -> Stack unit
   (requires (fun h -> live h new_root_key /\ live h new_chain_key /\
     live h our_ephemeral_priv_key /\ live h their_ephemeral_pub_key /\ live h root_key /\
     disjoint new_root_key new_chain_key /\
     disjoint new_root_key root_key /\
     disjoint new_root_key our_ephemeral_priv_key /\
     disjoint new_root_key their_ephemeral_pub_key /\
     disjoint new_chain_key root_key /\
     disjoint new_chain_key our_ephemeral_priv_key /\
     disjoint new_chain_key their_ephemeral_pub_key
   )) (ensures (fun h0 _ h1 ->
     modifies2 new_root_key new_chain_key h0 h1 /\ begin
       let (expected_new_root_key, expected_new_chain_key) = Spec.Signal.Core.ratchet
	 h0.[root_key] h0.[our_ephemeral_priv_key] h0.[their_ephemeral_pub_key]
       in
       h1.[new_root_key] == expected_new_root_key /\ h1.[new_chain_key] == expected_new_chain_key
     end
   ))

let ratchet new_root_key new_chain_key root_key our_ephemeral_priv_key their_ephemeral_pub_key =
  (**) let h0 = ST.get () in
  push_frame ();
  let shared_secret = create (size 32) (u8 0) in
  dh shared_secret our_ephemeral_priv_key their_ephemeral_pub_key;
  (**) let h1 = ST.get () in
  let keys =  create (size 64) (u8 0) in
  (**) recall_contents #uint8 #(size 14) const_label_WhisperRatchet
  (**)   (Spec.Signal.Messages.label_WhisperRatchet);
  (**) let h1' = ST.get () in
  hkdf2 #(Ghost.hide 14) keys shared_secret root_key (size 14) const_label_WhisperRatchet;
  (**) let h2 = ST.get () in
  copy new_root_key (sub keys (size 0) (size 32));
  copy new_chain_key (sub keys (size 32) (size 32));
  (**) let h3 = ST.get () in
  (**) Seq.eq_intro h1.[shared_secret] (Spec.Signal.Crypto.dh
  (**)   h0.[our_ephemeral_priv_key] h0.[their_ephemeral_pub_key]);
  (**) Seq.eq_intro h2.[keys] (Spec.Signal.Crypto.hkdf2
  (**)   h1.[shared_secret] h1.[root_key]
  (**)  (as_seq h1' const_label_WhisperRatchet));
  (**) Seq.eq_intro h3.[new_root_key] (
  (**)   let (expected_new_root_key, expected_new_chain_key) = Spec.Signal.Core.ratchet
  (**)     h0.[root_key] h0.[our_ephemeral_priv_key] h0.[their_ephemeral_pub_key]
  (**)   in expected_new_root_key
  (**) );
  (**) Seq.eq_intro h3.[new_chain_key] (
  (**)   let (expected_new_root_key, expected_new_chain_key) = Spec.Signal.Core.ratchet
  (**)     h0.[root_key] h0.[our_ephemeral_priv_key] h0.[their_ephemeral_pub_key]
  (**)   in expected_new_chain_key
  (**) );
  pop_frame ();
  ()



val lemma_concat5_right:
    #a:Type0
  -> len0:size_nat
  -> s0:Lib.Sequence.lseq a len0
  -> len1:size_nat{len0 + len1 <= max_size_t}
  -> s1:Lib.Sequence.lseq a len1
  -> len2:size_nat{len0 + len1 + len2 <= max_size_t}
  -> s2:Lib.Sequence.lseq a len2
  -> len3:size_nat{len0 + len1 + len2 + len3 <= max_size_t}
  -> s3:Lib.Sequence.lseq a len3
  -> len4:size_nat{len0 + len1 + len2 + len3 + len4 <= max_size_t}
  -> s4:Lib.Sequence.lseq a len4
  -> s:Lib.Sequence.lseq a (len0 + len1 + len2 + len3 + len4) ->
  Lemma
    (requires
      Lib.Sequence.sub s 0 len0 == s0 /\
      Lib.Sequence.sub s len0 len1 == s1 /\
      Lib.Sequence.sub s (len0 + len1) len2 == s2 /\
      Lib.Sequence.sub s (len0 + len1 + len2) len3 == s3 /\
      Lib.Sequence.sub s (len0 + len1 + len2 + len3) len4 == s4)
   (ensures s == Lib.Sequence.concat s0 (Lib.Sequence.concat s1
     (Lib.Sequence.concat s2 (Lib.Sequence.concat s3 s4))))


let lemma_concat5_right #a len0 s0 len1 s1 len2 s2 len3 s3 len4 s4 s =
  let s' = Lib.Sequence.concat s0 (Lib.Sequence.concat s1
    (Lib.Sequence.concat s2 (Lib.Sequence.concat s3 s4))) in
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s (len0 + len1 + len2) (len3 + len4)) len3;
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s' (len0 + len1 + len2) (len3 + len4)) len3;
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s (len0 + len1) (len2 + len3 + len4)) len2;
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s' (len0 + len1) (len2 + len3 + len4)) len2;
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s len0 (len1 + len2 + len3 + len4)) len1;
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s' len0 (len1 + len2 + len3 + len4)) len1;
  FStar.Seq.Properties.lemma_split s len0;
  FStar.Seq.Properties.lemma_split s' len0


#set-options "--z3rlimit 200 --fuel 0 --ifuel 0"

inline_for_extraction noextract val initiate':
    output: lbuffer uint8 (size 32)
  -> our_identity_priv_key: privkey_p
  -> our_onetime_priv_key: privkey_p
  -> their_identity_pub_key: pubkey_p
  -> their_signed_pub_key: pubkey_p
  -> their_onetime_pub_key: pubkey_p
  -> defined_their_onetime_pub_key: bool ->
  Stack unit
    (requires (fun h -> live h output /\ live h our_identity_priv_key /\ live h our_onetime_priv_key
                   /\ live h their_identity_pub_key /\ live h their_signed_pub_key
		   /\ live h their_onetime_pub_key
                   /\ disjoint output our_identity_priv_key
                   /\ disjoint output our_onetime_priv_key
                   /\ disjoint output their_identity_pub_key
                   /\ disjoint output their_signed_pub_key
                   /\ disjoint output their_onetime_pub_key))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1 /\
      h1.[output] == Spec.Signal.Core.initiate'
	h0.[our_identity_priv_key] h0.[our_onetime_priv_key]
	h0.[their_identity_pub_key] h0.[their_signed_pub_key]
	(if defined_their_onetime_pub_key then Some(h0.[their_onetime_pub_key]) else None)))

inline_for_extraction noextract
let initiate' output our_identity_priv_key our_onetime_priv_key their_identity_pub_key their_signed_pub_key their_onetime_pub_key defined_their_onetime_pub_key =
  // BB 2019/12/6 -> Timed out
  admit();
  push_frame ();
  (**) let h0 = ST.get () in
  let shared_secret = create (size 160) (u8 0xff) in
  let ff  = sub shared_secret (size 0) (size 32) in
  let dh1 = sub shared_secret (size 32) (size 32) in
  let dh2 = sub shared_secret (size 64) (size 32) in
  let dh3 = sub shared_secret (size 96) (size 32) in
  let dh4 = sub shared_secret (size 128) (size 32) in
  (**) recall_contents #uint8 #(size 32) const_ff
  (**)   Spec.Signal.Messages.ff;
  copy #IMMUT #uint8 #(size 32) ff const_ff;
  dh dh1 our_identity_priv_key their_signed_pub_key;
  dh dh2 our_onetime_priv_key their_identity_pub_key;
  dh dh3 our_onetime_priv_key their_signed_pub_key;
  let sz =
    if defined_their_onetime_pub_key then begin
      dh dh4 our_onetime_priv_key their_onetime_pub_key;
      (size (5 * 32))
    end else (size (4 * 32))
  in
  let correct_shared_secret : lbuffer uint8 sz =
    sub #MUT #uint8 #(size 160) shared_secret (size 0) sz
  in
  (**) let h1 = ST.get() in
  (**) if defined_their_onetime_pub_key then begin
  (**)	 lemma_concat5_right
  (**)     32 Spec.Signal.Messages.ff
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_identity_priv_key] h0.[their_signed_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_onetime_priv_key] h0.[their_identity_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_onetime_priv_key] h0.[their_signed_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_onetime_priv_key] h0.[their_onetime_pub_key])
  (**)     h1.[correct_shared_secret]
  (**) end else begin
  (**)   Impl.Signal.Messages.lemma_concat4_right
  (**)     32 Spec.Signal.Messages.ff
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_identity_priv_key] h0.[their_signed_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_onetime_priv_key] h0.[their_identity_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_onetime_priv_key] h0.[their_signed_pub_key])
  (**)     h1.[correct_shared_secret]
  (**) end;
  (**) recall_contents #uint8 #vsize_label_WhisperText const_label_WhisperText
  (**)   Spec.Signal.Messages.label_WhisperText;
  (**) recall_contents #uint8 #(size 32) const_zz Spec.Signal.Messages.zz;
  hkdf1 #(Ghost.hide (size_v sz)) #(Ghost.hide (size_v vsize_label_WhisperText))
    output sz correct_shared_secret const_zz vsize_label_WhisperText const_label_WhisperText;
  pop_frame()


val initiate:
     new_root_key:privkey_p
  -> new_chain_key: privkey_p
  -> our_identity_priv_key: privkey_p
  -> base_priv_key: privkey_p
  -> our_onetime_priv_key: privkey_p
  -> their_identity_pub_key: pubkey_p
  -> their_signed_pub_key: pubkey_p
  -> their_onetime_pub_key: pubkey_p
  -> defined_their_onetime_pub_key: bool ->
  Stack unit
    (requires (fun h -> live h new_root_key /\ live h our_identity_priv_key
		   /\ live h our_onetime_priv_key /\ live h their_identity_pub_key
		   /\ live h their_signed_pub_key /\ live h new_chain_key /\ live h base_priv_key
		   /\ live h their_onetime_pub_key
		   /\ disjoint new_root_key new_chain_key
                   /\ disjoint new_root_key our_identity_priv_key
		   /\ disjoint new_root_key base_priv_key
                   /\ disjoint new_root_key our_onetime_priv_key
                   /\ disjoint new_root_key their_identity_pub_key
                   /\ disjoint new_root_key their_signed_pub_key
                   /\ disjoint new_root_key their_onetime_pub_key
		   /\ disjoint new_chain_key our_identity_priv_key
                   /\ disjoint new_chain_key our_onetime_priv_key
		   /\ disjoint new_chain_key base_priv_key
                   /\ disjoint new_chain_key their_identity_pub_key
                   /\ disjoint new_chain_key their_signed_pub_key
                   /\ disjoint new_chain_key their_onetime_pub_key
    ))
    (ensures  (fun h0 _ h1 -> modifies2 new_root_key new_chain_key h0 h1 /\
      begin
        let (expected_root_key, expected_chain_key) = Spec.Signal.Core.initiate
	  h0.[our_identity_priv_key] h0.[base_priv_key]
	  h0.[our_onetime_priv_key] h0.[their_identity_pub_key]
	  h0.[their_signed_pub_key]
	  (if defined_their_onetime_pub_key then Some h0.[their_onetime_pub_key] else None)
        in
        h1.[new_root_key] == expected_root_key /\
        h1.[new_chain_key] == expected_chain_key
      end
    ))

let initiate new_root_key new_chain_key our_identity_priv_key base_priv_key our_onetime_priv_key
  their_identity_pub_key their_signed_pub_key their_onetime_pub_key defined_their_onetime_pub_key =
  push_frame ();
  let root_key = create (size 32) (u8 0) in
  initiate' root_key our_identity_priv_key base_priv_key their_identity_pub_key
    their_signed_pub_key their_onetime_pub_key defined_their_onetime_pub_key;
  ratchet new_root_key new_chain_key root_key our_onetime_priv_key their_signed_pub_key;
  pop_frame ()


val respond:
     output: privkey_p
  -> our_identity_priv_key: privkey_p
  -> our_signed_priv_key: privkey_p
  -> our_onetime_priv_key: privkey_p
  -> defined_our_onetime_priv_key: bool
  -> their_identity_pub_key: pubkey_p
  -> their_onetime_pub_key: pubkey_p ->
  Stack unit
    (requires (fun h -> live h output /\ live h our_identity_priv_key /\ live h our_signed_priv_key
                   /\ live h our_onetime_priv_key /\ live h their_identity_pub_key
		   /\ live h their_onetime_pub_key
                   /\ disjoint output our_identity_priv_key
                   /\ disjoint output our_signed_priv_key
                   /\ disjoint output our_onetime_priv_key
                   /\ disjoint output their_identity_pub_key
                   /\ disjoint output their_onetime_pub_key
    ))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1 /\
      h1.[output] == Spec.Signal.Core.respond h0.[our_identity_priv_key] h0.[our_signed_priv_key]
      (if defined_our_onetime_priv_key then Some h0.[our_onetime_priv_key] else None)
      h0.[their_identity_pub_key] h0.[their_onetime_pub_key]
    ))

let respond output our_identity_priv_key our_signed_priv_key our_onetime_priv_key defined_our_onetime_priv_key their_identity_pub_key their_onetime_pub_key =
  // BB 2019/12/6 -> Timed out
  admit();
  push_frame ();
  (**) let h0 = ST.get () in
  (**) let shared_secret = create (size 160) (u8 0xff) in
  let ff = sub shared_secret (size 0) (size 32) in
  let dh1 = sub shared_secret (size 32) (size 32) in
  let dh2 = sub shared_secret (size 64) (size 32) in
  let dh3 = sub shared_secret (size 96) (size 32) in
  let dh4 = sub shared_secret (size 128) (size 32) in
  let h0 = ST.get () in
  (**) recall_contents #uint8 #(size 32) const_ff Spec.Signal.Messages.ff;
  copy #IMMUT #uint8 #(size 32) ff const_ff;
  dh dh1 our_signed_priv_key their_identity_pub_key;
  dh dh2 our_identity_priv_key their_onetime_pub_key;
  dh dh3 our_signed_priv_key their_onetime_pub_key;
  let sz =
    if defined_our_onetime_priv_key then begin
        dh dh4 our_onetime_priv_key their_onetime_pub_key;
      (size (5 * 32)) end
     else (size (4 * 32))
  in
  let correct_shared_secret : lbuffer uint8 sz =
    sub #MUT #uint8 #(size 160) shared_secret (size 0) sz
  in
  (**) let h1 = ST.get () in
  (**) if defined_our_onetime_priv_key then begin
  (**)   lemma_concat5_right
  (**)     32 Spec.Signal.Messages.ff
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_signed_priv_key] h0.[their_identity_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_identity_priv_key] h0.[their_onetime_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_signed_priv_key] h0.[their_onetime_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_onetime_priv_key] h0.[their_onetime_pub_key])
  (**)     h1.[correct_shared_secret]
  (**) end else begin
  (**)   Impl.Signal.Messages.lemma_concat4_right
  (**)     32 Spec.Signal.Messages.ff
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_signed_priv_key] h0.[their_identity_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_identity_priv_key] h0.[their_onetime_pub_key])
  (**)     32 (Spec.Signal.Crypto.dh h0.[our_signed_priv_key] h0.[their_onetime_pub_key])
  (**)     h1.[correct_shared_secret]
  (**) end;
  (**) recall_contents #uint8 #(size 32) const_zz Spec.Signal.Messages.zz;
  (**) recall_contents #uint8 #vsize_label_WhisperText const_label_WhisperText
  (**)   Spec.Signal.Messages.label_WhisperText;
  hkdf1 #(Ghost.hide (size_v sz)) #(Ghost.hide (size_v vsize_label_WhisperText))
    output sz correct_shared_secret const_zz vsize_label_WhisperText const_label_WhisperText;
  pop_frame ()


val fill_message_keys:
     msg_key:privkey_p
  -> new_chain_key:privkey_p
  -> chain_key:privkey_p
  -> Stack unit
    (requires (fun h -> live h msg_key /\ live h new_chain_key /\ live h chain_key /\
      disjoint msg_key new_chain_key /\ disjoint msg_key chain_key /\
      disjoint new_chain_key chain_key
    ))
    (ensures (fun h0 _ h1 -> modifies2 new_chain_key msg_key h0 h1 /\
      begin let (expected_msg_key, expected_chain_key) = Spec.Signal.Core.fill_message_keys
	h0.[chain_key]
      in
      expected_msg_key == h1.[msg_key] /\ expected_chain_key == h1.[new_chain_key]
      end
    ))

let fill_message_keys msg_key new_chain_key chain_key =
  (**) recall_contents #uint8 #(size 1) const_one Spec.Signal.Messages.one;
  hmac #(Ghost.hide 1) msg_key chain_key (size 1) const_one;
  (**) recall_contents #uint8 #(size 1) const_two Spec.Signal.Messages.two;
  hmac #(Ghost.hide 1) new_chain_key chain_key (size 1) const_two



noextract
val serialize_and_add_mac_spec:
     #plen:(Ghost.erased size_nat){
       Ghost.reveal plen + 16 <= max_size_t /\
       Spec.Signal.Crypto.cipherlen (Ghost.reveal plen) + 140 + 64 <= max_size_t
     }
  -> our_identity_pub_key: Spec.Signal.Crypto.pubkey
  -> their_identity_pub_key: Spec.Signal.Crypto.pubkey
  -> our_ephemeral_pub_key: Spec.Signal.Crypto.pubkey
  -> prev_counter:size_t
  -> counter:size_t
  -> ciphertext: Seq.lseq uint8 (Spec.Signal.Crypto.cipherlen (Ghost.reveal plen))
  -> mac_key: Spec.Signal.Crypto.privkey
  -> Tot (r:Seq.seq uint8{
    Seq.length r = Spec.Signal.Core.encrypt_get_length (v prev_counter) (v counter) (Ghost.reveal plen)
  })

noextract
let serialize_and_add_mac_spec #plen our_identity_pub_key their_identity_pub_key
  our_ephemeral_pub_key prev_counter counter ciphertext mac_key =
  let gwhisper_msg = Spec.Signal.Messages.serialize_whisper_message
     our_ephemeral_pub_key (v prev_counter) (v counter)
     ciphertext
  in
  let gtag8 = Spec.Signal.Messages.mac_whisper_msg mac_key
    their_identity_pub_key our_identity_pub_key gwhisper_msg
  in
  let c0 = Seq.create 1 (((u8 3) <<. 4ul) |. (u8 3)) in
  Seq.concat (Seq.concat c0 (Seq.to_lseq gwhisper_msg)) gtag8


inline_for_extraction noextract
val serialize_and_add_mac:
    #vplen:(Ghost.erased size_nat){
      Ghost.reveal vplen + 16 <= max_size_t /\
      Spec.Signal.Crypto.cipherlen (Ghost.reveal vplen) + 16 + 57 + 128 + 33 + 32 <= max_size_t
    }
  -> #vclen:(Ghost.erased size_nat){Ghost.reveal vclen =
    Spec.Signal.Crypto.cipherlen (Ghost.reveal vplen)}
  -> olen: size_t{v olen = Spec.Signal.Core.size_encrypt_max_length (Ghost.reveal vplen)}
  -> output:lbuffer uint8 olen
  -> tag8: lbuffer uint8 (size 8)
  -> our_identity_pub_key:pubkey_p
  -> their_identity_pub_key:pubkey_p
  -> our_ephemeral_pub_key:pubkey_p
  -> prev_counter:size_t
  -> counter:size_t
  -> clen:size_t{v clen = Ghost.reveal vclen}
  -> ciphertext:lbuffer uint8 clen
  -> mac_key: privkey_p->
  Stack size_t
   (requires (fun h -> live h output /\ live h tag8 /\ live h our_identity_pub_key
		 /\ live h their_identity_pub_key /\ live h mac_key
                 /\ live h our_ephemeral_pub_key /\ live h ciphertext
                 /\ disjoint output our_identity_pub_key
                 /\ disjoint output their_identity_pub_key
                 /\ disjoint output our_ephemeral_pub_key
                 /\ disjoint output ciphertext
		 /\ disjoint output mac_key
		 /\ disjoint output tag8
		 /\ disjoint tag8 our_identity_pub_key
                 /\ disjoint tag8 their_identity_pub_key
                 /\ disjoint tag8 our_ephemeral_pub_key
                 /\ disjoint tag8 ciphertext
		 /\ disjoint tag8 mac_key
  ))
  (ensures  (fun h0 wmlen h1 -> modifies2 tag8 output h0 h1 /\
     v wmlen = Spec.Signal.Core.encrypt_get_length
       (v prev_counter) (v counter) (Ghost.reveal vplen) /\
     Seq.sub h1.[output] 0 (v wmlen) == serialize_and_add_mac_spec #vplen
       h0.[our_identity_pub_key]
       h0.[their_identity_pub_key]
       h0.[our_ephemeral_pub_key]
       prev_counter
       counter
       h0.[ciphertext]
       h0.[mac_key]
  ))

inline_for_extraction noextract
let serialize_and_add_mac #vplen #vclen olen output tag8
  our_identity_pub_key their_identity_pub_key our_ephemeral_pub_key prev_counter counter clen
  ciphertext mac_key =
  (**) let h0 = ST.get () in
  let output1 = sub output (size 0) (size 1) in
  (**) recall_contents #uint8 #(size 1) const_fifty_one Spec.Signal.Messages.fifty_one;
  copy #IMMUT #uint8 #(size 1) output1 const_fifty_one;
  let h1 = ST.get () in
  (**) Seq.eq_intro h1.[output1] Spec.Signal.Messages.fifty_one;
  (**) Spec.Signal.Messages.lemma_fifty_one ();
  let maxwmlen = clen +. (size 57) in
  (* Compute the whisper_msg *)
  let whisper_msg = sub output (size 1) maxwmlen in
  (**) assert(Ghost.reveal vclen + 57 <= max_size_t);
  let wmlen = serialize_whisper_message #vclen clen
    whisper_msg our_ephemeral_pub_key prev_counter counter ciphertext in
  (* Compute the tag *)
  let output2 = sub output (size 1) wmlen in
  let h2 = ST.get () in
  (**) Seq.eq_intro (Seq.sub h2.[whisper_msg] 0 (v wmlen)) h2.[output2];
  (**) Seq.eq_intro h2.[output2] (
  (**)   Spec.Signal.Messages.serialize_whisper_message
  (**)	    h0.[our_ephemeral_pub_key] (v prev_counter) (v counter)
  (**)	    h0.[ciphertext]
  (**) );
  mac_whisper_msg #(Ghost.hide (size_v wmlen)) tag8 mac_key their_identity_pub_key
    our_identity_pub_key wmlen output2;
  (**) let h3 = ST.get () in
  (**) Seq.eq_intro h3.[tag8] (
  (**)   let gwhisper_msg = Spec.Signal.Messages.serialize_whisper_message
  (**)	   h0.[our_ephemeral_pub_key] (v prev_counter) (v counter)
  (**)	   h0.[ciphertext]
  (**)   in Spec.Signal.Messages.mac_whisper_msg h0.[mac_key]
  (**)     h0.[their_identity_pub_key] h0.[our_identity_pub_key] gwhisper_msg
  (**) );
  let output3 = sub output (wmlen +! size 1) (size 8) in
  assert(disjoint output3 output1);
  assert(disjoint output3 output2);
  copy #MUT #uint8 #(size 8) output3 tag8;
  (**) let h4 = ST.get () in
  (**) Seq.lemma_concat3
  (**)   1 h4.[output1]
  (**)   (v wmlen) h4.[output2]
  (**)   8 h4.[output3]
  (**)   (Seq.sub h4.[output] 0 (v wmlen + 9));
  let flen = wmlen +! size 9 in
  (**) assert(v wmlen = Spec.Signal.Messages.serialize_whisper_message_get_length
  (**)   (v prev_counter) (v counter) (Ghost.reveal vclen));
  (**) assert(v flen = Spec.Signal.Core.encrypt_get_length (v prev_counter) (v counter)
  (**)   (Ghost.reveal vplen));
  (**) Seq.eq_intro (Seq.sub h4.[output] 0 (v flen))
  (**)   begin
  (**)     let gwhisper_msg = Spec.Signal.Messages.serialize_whisper_message
  (**)       h0.[our_ephemeral_pub_key] (v prev_counter) (v counter)
  (**)       h0.[ciphertext]
  (**)     in
  (**)     let gtag8 = Spec.Signal.Messages.mac_whisper_msg h0.[mac_key]
  (**)       h0.[their_identity_pub_key] h0.[our_identity_pub_key] gwhisper_msg
  (**)     in
  (**)     let c0 = Seq.create 1 (((u8 3) <<. 4ul) |. (u8 3)) in
  (**)     Seq.concat (Seq.concat c0 (Seq.to_lseq gwhisper_msg)) gtag8
  (**)   end;
  flen


noextract
val encrypt_from_msg_key_spec:
     #plen:(Ghost.erased size_nat){
       Ghost.reveal plen + 16 <= max_size_t /\
       Spec.Signal.Crypto.cipherlen (Ghost.reveal plen) + 265 <= max_size_t
     }
  -> msg_key: Spec.Signal.Crypto.privkey
  -> counter: size_t
  -> plaintext: Seq.lseq uint8 (Ghost.reveal plen)
  -> Tot (Seq.lseq uint8 (Spec.Signal.Crypto.cipherlen (Ghost.reveal plen)) &
    Spec.Signal.Crypto.privkey)

noextract
let encrypt_from_msg_key_spec #plen msg_key counter plaintext =
  let gkeys = Spec.Signal.Crypto.hkdf3 msg_key
    Spec.Signal.Messages.zz Spec.Signal.Messages.label_WhisperMessageKeys
  in
  let enc_key = Seq.sub gkeys 0 32 in
  let mac_key = Seq.sub gkeys 32 32 in
  let enc_iv  = Seq.sub gkeys 64 16 in
  let ciphertext = Spec.Signal.Crypto.aes_enc enc_key enc_iv plaintext in
  (ciphertext, mac_key)


inline_for_extraction noextract
val encrypt_from_msg_key:
     #vplen:(Ghost.erased size_nat){
       Ghost.reveal vplen > 0 /\
       Ghost.reveal vplen + 16 <= max_size_t /\
       Spec.Signal.Crypto.cipherlen (Ghost.reveal vplen) + 265 <= max_size_t
     }
  -> keys:lbuffer uint8 (size 96)
  -> len:size_t{v len = Ghost.reveal vplen}
  -> ciphertext: lbuffer uint8 (len +! size 16)
  -> msg_key: privkey_p
  -> counter: size_t
  -> plaintext: lbuffer uint8 len
  -> Stack unit
    (requires (fun h -> live h keys /\ live h msg_key  /\ live h plaintext /\
      live h ciphertext /\
      disjoint keys msg_key /\
      disjoint keys plaintext /\
      disjoint ciphertext msg_key /\
      disjoint ciphertext keys /\
      disjoint ciphertext plaintext
    )) (ensures (fun h0 _ h1 -> modifies2 keys ciphertext h0 h1 /\

      begin
        let (expected_ciphertext, mac_key) =
	  encrypt_from_msg_key_spec #vplen h0.[msg_key] counter h0.[plaintext]
	in
        Seq.sub h1.[ciphertext] 0 (Spec.Signal.Crypto.cipherlen (Ghost.reveal vplen)) ==
	  expected_ciphertext /\
	Seq.sub h1.[keys] 32 32 == mac_key
      end
    ))

inline_for_extraction noextract
let encrypt_from_msg_key #vplen keys len ciphertext msg_key
  counter plaintext
  =
  (**) let h0 = ST.get () in
  (**) recall_contents #uint8 #(size 32) const_zz Spec.Signal.Messages.zz;
  (**) recall_contents #uint8 #vsize_label_WhisperMessageKeys const_label_WhisperMessageKeys
  (**)   Spec.Signal.Messages.label_WhisperMessageKeys;
  hkdf3 #(Ghost.hide (size_v vsize_label_WhisperMessageKeys))
    keys msg_key const_zz
    vsize_label_WhisperMessageKeys const_label_WhisperMessageKeys;
  (**) let h1 = ST.get () in
  (**) Seq.eq_intro h1.[keys] (Spec.Signal.Crypto.hkdf3 h0.[msg_key]
  (**)   Spec.Signal.Messages.zz Spec.Signal.Messages.label_WhisperMessageKeys);
  let enc_key = sub #MUT #uint8 #(size 96) keys (size 0) (size 32) in
  let mac_key = sub #MUT #uint8 #(size 96) keys (size 32) (size 32) in
  let enc_iv  = sub #MUT #uint8 #(size 96) keys (size 64) (size 16) in
  let clen = cipherlen len in
  (* Compute the ciphertext *)
  enc #vplen len ciphertext enc_key enc_iv plaintext


let encrypt_get_length
    (prev_counter:size_t)
    (counter:size_t)
    (plen:size_t{v plen + 16 <= max_size_t /\ Spec.Signal.Crypto.cipherlen (v plen) + 140 + 64 <= max_size_t})
    : Tot (r:size_t{v r == Spec.Signal.Core.encrypt_get_length (v prev_counter) (v counter) (v plen)}) =
    1ul +. (serialize_whisper_message_get_length prev_counter counter (cipherlen plen)) +. 8ul


noextract
val encrypt_spec:
    #plen:(Ghost.erased size_nat){
      Ghost.reveal plen + 16 <= max_size_t /\
      Spec.Signal.Crypto.cipherlen (Ghost.reveal plen) + 265 <= max_size_t
    }
  -> our_identity_pub_key: Spec.Signal.Crypto.pubkey
  -> their_identity_pub_key: Spec.Signal.Crypto.pubkey
  -> msg_key: Spec.Signal.Crypto.privkey
  -> our_ephemeral_pub_key: Spec.Signal.Crypto.pubkey
  -> prev_counter:size_t
  -> counter:size_t
  -> plaintext:Seq.lseq uint8 (Ghost.reveal plen)
  -> Pure (
    Seq.lseq uint8
      (Spec.Signal.Core.encrypt_get_length (v prev_counter) (v counter) (Ghost.reveal plen))
    )
    (requires (True))
    (ensures (fun out ->
      let expected_output =
        Spec.Signal.Core.encrypt our_identity_pub_key their_identity_pub_key msg_key
	  our_ephemeral_pub_key (v prev_counter) (v counter) plaintext
      in
      let output = out in
      output == expected_output
    ))

noextract
let encrypt_spec #plen our_identity_pub_key their_identity_pub_key msg_key our_ephemeral_pub_key
  prev_counter counter plaintext =
  let (ciphertext, mac_key) =
    encrypt_from_msg_key_spec #plen msg_key counter plaintext
  in
  let output =
    serialize_and_add_mac_spec #plen our_identity_pub_key their_identity_pub_key
      our_ephemeral_pub_key prev_counter counter ciphertext mac_key
  in
  output


val encrypt:
    #vplen:(Ghost.erased size_nat){
      Ghost.reveal vplen > 0 /\
      Ghost.reveal vplen + 16 <= max_size_t /\
      Spec.Signal.Crypto.cipherlen (Ghost.reveal vplen) + 265 <= max_size_t
    }
  -> olen: size_t{size_v olen = Spec.Signal.Core.size_encrypt_max_length (Ghost.reveal vplen)}
  -> output: lbuffer uint8 olen
  -> our_identity_pub_key: pubkey_p
  -> their_identity_pub_key: pubkey_p
  -> msg_key: key_p
  -> our_ephemeral_pub_key: pubkey_p
  -> prev_counter: size_t
  -> counter: size_t
  -> len: size_t{size_v len = Ghost.reveal vplen}
  -> plaintext: lbuffer uint8 len->
  Stack size_t
  (requires (fun h -> live h output /\ live h our_identity_pub_key
		 /\ live h their_identity_pub_key
                 /\ live h msg_key /\ live h our_ephemeral_pub_key /\ live h plaintext
                 /\ disjoint output our_identity_pub_key
                 /\ disjoint output their_identity_pub_key
                 /\ disjoint output msg_key
                 /\ disjoint output our_ephemeral_pub_key
                 /\ disjoint output plaintext
  ))
  (ensures  (fun h0 wmlen h1 -> modifies1 output h0 h1 /\
     v wmlen = Spec.Signal.Core.encrypt_get_length
       (size_v prev_counter) (size_v counter) (Ghost.reveal vplen) /\
     begin
       let expected_output = encrypt_spec #vplen
         h0.[our_identity_pub_key] h0.[their_identity_pub_key] h0.[msg_key]
         h0.[our_ephemeral_pub_key] prev_counter counter h0.[plaintext]
       in
       expected_output == Seq.sub h1.[output] 0 (v wmlen)
     end
  ))

let encrypt #vplen olen output our_identity_pub_key their_identity_pub_key msg_key our_ephemeral_pub_key prev_counter counter len plaintext =
  push_frame ();
  (**) let h0 = ST.get () in
  let maxclen = len +! (size 16) in
  let maxwmlen = maxclen +! (size 57) in
  let max = maxwmlen +! (size 96) in
  let scratch = create max (u8 0) in
  let keys = sub #MUT #uint8 #max  scratch (size 0) (size 96) in
  let ciphertext = sub #MUT #uint8 #max scratch (size 96) maxclen in
  let tag8 = sub #MUT #uint8 #max scratch ((size 96) +! maxclen) (size 8) in
  (**) assert(disjoint tag8 ciphertext /\ disjoint tag8 keys);
  (**) assert(disjoint ciphertext keys);
  encrypt_from_msg_key #vplen keys len ciphertext msg_key counter plaintext;
  let mac_key = sub #MUT #uint8 #(size 96) keys (size 32) (size 32) in
  (**) let h2 = ST.get () in
  (**) Seq.eq_intro
  (**)   (Seq.sub h2.[ciphertext] 0 (Spec.Signal.Crypto.cipherlen (size_v len))) (
  (**)   let (expected_ciphertext, _) =
  (**)      encrypt_from_msg_key_spec #vplen h0.[msg_key] counter h0.[plaintext]
  (**)   in expected_ciphertext);
  (**) Seq.eq_intro h2.[mac_key] (
  (**)  let (_, expected_mac_key) =
  (**)     encrypt_from_msg_key_spec #vplen h0.[msg_key] counter h0.[plaintext]
  (**)  in expected_mac_key);
  let clen = cipherlen len in
  let correct_ciphertext = sub #MUT #uint8 #maxclen ciphertext (size 0) clen in
  (**) assert(disjoint correct_ciphertext tag8 /\ disjoint correct_ciphertext mac_key);
  (**) assert(disjoint tag8 mac_key);
  let flen = serialize_and_add_mac #vplen
    #(Ghost.hide (Spec.Signal.Crypto.cipherlen (Ghost.reveal vplen)))
    olen output tag8 our_identity_pub_key their_identity_pub_key
    our_ephemeral_pub_key prev_counter counter clen correct_ciphertext mac_key
  in
  (**) assert(size_v flen = Spec.Signal.Core.encrypt_get_length
  (**)   (v prev_counter) (v counter) (Ghost.reveal vplen));
  (**) let h3 = ST.get () in
  (**) Seq.eq_intro (Seq.sub h3.[output] 0 (size_v flen)) (serialize_and_add_mac_spec #vplen
  (**)   h0.[our_identity_pub_key]
  (**)   h0.[their_identity_pub_key]
  (**)   h0.[our_ephemeral_pub_key]
  (**)   prev_counter
  (**)   counter
  (**)   h2.[correct_ciphertext]
  (**)   h2.[mac_key]);
  pop_frame ();
  flen


noextract val decrypt_serialize_and_compare_tag_spec:
     their_ephemeral_pub_key: Spec.Signal.Crypto.pubkey
  -> mac_key: Spec.Signal.Crypto.key
  -> our_identity_pub_key: Spec.Signal.Crypto.pubkey
  -> their_identity_pub_key: Spec.Signal.Crypto.pubkey
  -> prev_counter: size_nat
  -> counter: size_nat
  -> ciphertext: Spec.Signal.Messages.cipher_bytes
  -> tag8: Seq.lseq uint8 8
  -> Tot bool

noextract let decrypt_serialize_and_compare_tag_spec their_ephemeral_pub_key mac_key our_identity_pub_key
  their_identity_pub_key prev_counter counter ciphertext tag8 =
  let whisper_message =
    Spec.Signal.Messages.serialize_whisper_message their_ephemeral_pub_key
      prev_counter counter ciphertext
  in
  let exp_tag8 =
    Spec.Signal.Messages.mac_whisper_msg mac_key our_identity_pub_key
      their_identity_pub_key whisper_message
  in
  Spec.Signal.Messages.equal_bytes tag8 exp_tag8


inline_for_extraction noextract val decrypt_serialize_and_compare_tag:
     #volen: Ghost.erased size_nat
  -> #vclen: (Ghost.erased size_nat){
      (Ghost.reveal vclen) + Spec.Signal.Messages.size_whisper_message_extra_info <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) +
        Spec.Signal.Messages.size_mac_whisper_msg_extra_info + 32 + 64 <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) + 1 <=
	(Ghost.reveal volen) /\
      (Ghost.reveal vclen) > 0 /\ (Ghost.reveal vclen) % 16 = 0
    }
  -> olen: size_t{size_v olen = Ghost.reveal volen}
  -> output:lbuffer uint8 olen
  -> computed_tag8: lbuffer uint8 (size 8)
  -> their_ephemeral_pub_key: pubkey_p
  -> mac_key: privkey_p
  -> our_identity_pub_key: pubkey_p
  -> their_identity_pub_key: pubkey_p
  -> prev_counter: size_t
  -> counter: size_t
  -> clen: size_t{size_v clen = Ghost.reveal vclen}
  -> ciphertext: lbuffer uint8 clen
  -> tag8: lbuffer uint8 (size 8)
  -> Stack bool
    (requires (fun h -> live h their_ephemeral_pub_key /\ live h mac_key /\
      live h our_identity_pub_key /\ live h their_identity_pub_key /\
      live h ciphertext /\ live h tag8 /\
      live h output /\ live h computed_tag8 /\
      disjoint output computed_tag8 /\
      disjoint output their_ephemeral_pub_key /\
      disjoint output mac_key /\
      disjoint output our_identity_pub_key /\
      disjoint output their_identity_pub_key /\
      disjoint output ciphertext /\
      disjoint output tag8 /\
      disjoint computed_tag8 their_ephemeral_pub_key /\
      disjoint computed_tag8 mac_key /\
      disjoint computed_tag8 our_identity_pub_key /\
      disjoint computed_tag8 their_identity_pub_key /\
      disjoint computed_tag8 ciphertext /\
      disjoint computed_tag8 tag8
    ))
    (ensures (fun h0 b h1 -> modifies2 output computed_tag8 h0 h1 /\
      begin
	let expected_b = decrypt_serialize_and_compare_tag_spec h0.[their_ephemeral_pub_key]
          h0.[mac_key] h0.[our_identity_pub_key] h0.[their_identity_pub_key] (v prev_counter)
	  (v counter) h0.[ciphertext] h0.[tag8]
	in
	expected_b = b
      end
    ))


inline_for_extraction noextract
let decrypt_serialize_and_compare_tag #volen #vclen olen output
  computed_tag8 their_ephemeral_pub_key mac_key our_identity_pub_key their_identity_pub_key
   prev_counter counter clen ciphertext tag8 =
  (* Compute the whisper_msg *)
  (**) let h0 = ST.get () in
  assert(Ghost.reveal vclen + 57 <= max_size_t);
  let maxwmlen = clen +! (size 57) in
  let whisper_msg = sub #MUT #uint8 #olen output (size 1) maxwmlen in
  let wmlen = serialize_whisper_message #vclen clen whisper_msg their_ephemeral_pub_key
    prev_counter counter ciphertext
  in
  let correct_whisper_msg = sub whisper_msg (size 0) wmlen in
  (**) let h1 = ST.get () in
  (**) Seq.eq_intro h1.[correct_whisper_msg] (Spec.Signal.Messages.serialize_whisper_message
  (**)   h0.[their_ephemeral_pub_key] (v prev_counter) (v counter) h0.[ciphertext]);
  (**) assert(disjoint correct_whisper_msg computed_tag8 /\ disjoint computed_tag8 mac_key /\
  (**)   disjoint computed_tag8 our_identity_pub_key /\ disjoint computed_tag8
  (**)   their_identity_pub_key);
  (**) assert(v wmlen + Spec.Signal.Messages.size_mac_whisper_msg_extra_info + 32 <= max_size_t);
  (* Compute the tag *)
  mac_whisper_msg #(Ghost.hide (size_v wmlen)) computed_tag8 mac_key our_identity_pub_key
  their_identity_pub_key wmlen correct_whisper_msg;
  (**) let h2 = ST.get () in
  (**) Seq.eq_intro h2.[computed_tag8] (Spec.Signal.Messages.mac_whisper_msg h1.[mac_key]
  (**)   h0.[our_identity_pub_key] h0.[their_identity_pub_key] h1.[correct_whisper_msg]);
  let res = equal_bytes #(Ghost.hide 8) (size 8) tag8 computed_tag8 in
  (**) assert(res = Spec.Signal.Messages.equal_bytes h0.[tag8] h2.[computed_tag8]);
  res


noextract val decrypt_compute_keys_spec:
     msg_key: Spec.Signal.Crypto.key
  -> counter: size_nat
  -> Tot (Seq.lseq uint8 96)

noextract let decrypt_compute_keys_spec msg_key counter  =
  let keys = Spec.Signal.Crypto.hkdf3 msg_key Spec.Signal.Messages.zz
    Spec.Signal.Messages.label_WhisperMessageKeys
  in
  keys


inline_for_extraction noextract
val decrypt_compute_keys:
     keys: lbuffer uint8 (size 96)
  -> msg_key: privkey_p
  -> counter: size_t
  -> Stack unit
    (requires (fun h -> live h keys /\ live h msg_key /\
      disjoint keys msg_key
    ))
    (ensures (fun h0 _ h1 -> modifies1 keys h0 h1 /\
      begin
        let expected_keys =
	  decrypt_compute_keys_spec h0.[msg_key] (v counter)
	in
	expected_keys == h1.[keys]
      end
    ))

inline_for_extraction noextract
let decrypt_compute_keys keys msg_key counter =
  (**) let h0 = ST.get () in
  (* Compute the keys *)
  (**) recall_contents #uint8 #(size 32) const_zz Spec.Signal.Messages.zz;
  (**) recall_contents #uint8 #vsize_label_WhisperMessageKeys const_label_WhisperMessageKeys
  (**)   Spec.Signal.Messages.label_WhisperMessageKeys;
  hkdf3 #(Ghost.hide (size_v vsize_label_WhisperMessageKeys)) keys msg_key const_zz
     vsize_label_WhisperMessageKeys const_label_WhisperMessageKeys;
  (**) let h2 = ST.get () in
  (**) Seq.eq_intro h2.[keys] (Spec.Signal.Crypto.hkdf3 h2.[msg_key] Spec.Signal.Messages.zz
  (**)   Spec.Signal.Messages.label_WhisperMessageKeys)


noextract val decrypt_dec_and_return_spec:
     enc_key: Spec.Signal.Crypto.key
  -> enc_iv: Seq.lseq uint8 16
  -> ciphertext: Spec.Signal.Messages.cipher_bytes
  -> Tot (option (Spec.Signal.Messages.plain_bytes))

noextract let decrypt_dec_and_return_spec enc_key enc_iv ciphertext =
  let plain = Spec.Signal.Crypto.aes_dec enc_key enc_iv ciphertext in
    match plain with
    | Some plain -> Some plain
    | None -> None


noextract val decrypt_return_post:
     #volen: Ghost.erased size_nat
  -> #vclen: (Ghost.erased size_nat){
      Ghost.reveal vclen + Spec.Signal.Messages.size_whisper_message_extra_info <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) +
        Spec.Signal.Messages.size_mac_whisper_msg_extra_info + 32 <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) + 1 <=
	(Ghost.reveal volen) /\
      (Ghost.reveal vclen) > 0 /\ Ghost.reveal vclen % 16 = 0
    }
  -> expected:option (Spec.Signal.Messages.plain_bytes)
  -> olen: size_t{size_v olen = Ghost.reveal volen}
  -> output: lbuffer uint8 olen
  -> plen:size_t{v plen <= Ghost.reveal volen}
  -> h0: mem
  -> h1: mem
  -> Type0


noextract let decrypt_return_post #volen #vclen expected olen output plen h0 h1 =
  if v plen = 0 then
    expected == None
  else match expected with
    | Some (expected_plaintext) ->
      v plen = Seq.length expected_plaintext /\
      Seq.sub h1.[output] 0 (v plen) == expected_plaintext
    | None -> False

inline_for_extraction noextract val decrypt_dec_and_return:
     #volen: Ghost.erased size_nat
  -> #vclen: (Ghost.erased size_nat){
      (Ghost.reveal vclen) + Spec.Signal.Messages.size_whisper_message_extra_info <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) +
        Spec.Signal.Messages.size_mac_whisper_msg_extra_info + 32 + 64 <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) + 1 <=
      (Ghost.reveal volen) /\
      Ghost.reveal vclen > 0 /\ Ghost.reveal vclen % 16 = 0
    }
 -> olen: size_t{size_v olen = Ghost.reveal volen}
 -> output: lbuffer uint8 olen
 -> enc_key: key_p
 -> enc_iv: lbuffer uint8 (size 16)
 -> clen: size_t{v clen = Ghost.reveal vclen}
 -> ciphertext: lbuffer uint8 clen
 -> Stack size_t
   (requires (fun h -> live h output /\ live h enc_key /\ live h enc_iv /\ live h ciphertext /\
     disjoint output enc_key /\
     disjoint output enc_iv /\
     disjoint output ciphertext
   ))
   (ensures (fun h0 plen h1 -> modifies1 output h0 h1 /\ v plen <= Ghost.reveal volen /\
     begin
       let expected = decrypt_dec_and_return_spec h0.[enc_key] h0.[enc_iv] h0.[ciphertext]
       in decrypt_return_post #volen #vclen expected olen output plen h0 h1
     end
   ))

inline_for_extraction noextract let decrypt_dec_and_return #volen #vclen olen output enc_key
  enc_iv clen ciphertext =
  (**) let h0 = ST.get () in
  let plaintext = sub output (size 0) clen in
  assert(disjoint plaintext enc_key /\ disjoint plaintext enc_iv /\ disjoint plaintext ciphertext);
  let plen = dec #vclen clen plaintext enc_key enc_iv ciphertext in
  (**) let h1 = ST.get () in
  (**) begin match Spec.Signal.Crypto.aes_dec h0.[enc_key] h0.[enc_iv] h0.[ciphertext] with
  (**)  | None ->
  (**)    assert(v plen = 0)
  (**)  | Some gplaintext ->
  (**)     (assert(v plen = Seq.length gplaintext);
  (**)      Seq.eq_intro (Seq.sub h1.[plaintext] 0 (v plen)) gplaintext)
  (**) end;
  plen


noextract val decrypt_branch_on_bad_tag_spec:
     equal_tag: bool
  -> enc_key: Spec.Signal.Crypto.privkey
  -> enc_iv: Seq.lseq uint8 16
  -> ciphertext: Spec.Signal.Messages.cipher_bytes
  -> Tot (option (Spec.Signal.Messages.plain_bytes))

noextract let decrypt_branch_on_bad_tag_spec equal_tag enc_key enc_iv ciphertext =
  if not equal_tag then
    None
  else
    decrypt_dec_and_return_spec enc_key enc_iv ciphertext


inline_for_extraction noextract val decrypt_branch_on_bad_tag:
     #volen: Ghost.erased size_nat
  -> #vclen: (Ghost.erased size_nat){
      Ghost.reveal vclen + Spec.Signal.Messages.size_whisper_message_extra_info <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) +
        Spec.Signal.Messages.size_mac_whisper_msg_extra_info + 32 + 64 <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) + 1 <=
	Ghost.reveal volen /\
      Ghost.reveal vclen > 0 /\ Ghost.reveal vclen % 16 = 0
    }
  -> olen: size_t{size_v olen = Ghost.reveal volen}
  -> output: lbuffer uint8 olen
  -> equal_tag: bool
  -> enc_key: privkey_p
  -> enc_iv: lbuffer uint8 (size 16)
  -> clen: size_t{v clen = Ghost.reveal vclen}
  -> ciphertext: lbuffer uint8 clen
  -> Stack size_t
    (requires (fun h -> live h output /\ live h enc_key /\ live h enc_iv /\ live h ciphertext /\
      disjoint output enc_key /\ disjoint output enc_iv /\
      disjoint output ciphertext
    ))
    (ensures (fun h0 plen h1 -> modifies1 output h0 h1 /\ v plen <= Ghost.reveal volen /\
     begin
       let expected = decrypt_branch_on_bad_tag_spec equal_tag h0.[enc_key] h0.[enc_iv]
         h0.[ciphertext]
       in decrypt_return_post #volen #vclen expected olen output plen h0 h1
     end
   ))

inline_for_extraction noextract let decrypt_branch_on_bad_tag #volen #vclen olen output equal_tag enc_key enc_iv ciphertext clen =
   if not equal_tag then begin
    (size 0)
  end else begin
    decrypt_dec_and_return #volen #vclen olen output enc_key enc_iv ciphertext clen
  end


noextract val decrypt_spec:
     our_identity_key: Spec.Signal.Crypto.pubkey
  -> their_identity_pub_key: Spec.Signal.Crypto.pubkey
  -> their_ephemeral_pub_key: Spec.Signal.Crypto.pubkey
  -> chain_key: Spec.Signal.Crypto.key
  -> prev_counter: size_nat
  -> counter: size_nat
  -> ciphertext: Spec.Signal.Messages.cipher_bytes
  -> tag8: Seq.lseq uint8 8
  ->  Pure (option (Spec.Signal.Messages.plain_bytes))
    (requires True)
    (ensures (fun result ->
      result == Spec.Signal.Core.decrypt our_identity_key their_identity_pub_key
	their_ephemeral_pub_key chain_key prev_counter counter ciphertext tag8))

noextract let decrypt_spec our_identity_pub_key their_identity_pub_key
  their_ephemeral_pub_key chain_key prev_counter counter ciphertext tag8 =
  let len = Seq.length ciphertext in
  let ciphertext = Seq.to_lseq ciphertext in
  let keys = decrypt_compute_keys_spec chain_key counter in
  let enc_key = Seq.sub keys 0 32 in
  let mac_key = Seq.sub keys 32 32 in
  let enc_iv  = Seq.sub keys 64 16 in
  let equal_tag = decrypt_serialize_and_compare_tag_spec their_ephemeral_pub_key mac_key
    our_identity_pub_key their_identity_pub_key prev_counter counter ciphertext tag8
  in
  decrypt_branch_on_bad_tag_spec equal_tag enc_key enc_iv ciphertext


val decrypt:
    #volen: Ghost.erased size_nat
  -> #vclen: (Ghost.erased size_nat){
      Ghost.reveal vclen + Spec.Signal.Messages.size_whisper_message_extra_info <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) +
        Spec.Signal.Messages.size_mac_whisper_msg_extra_info + 32 + 64 <= max_size_t /\
      Spec.Signal.Messages.max_whisper_message_len (Ghost.reveal vclen) + 1 <=
	Ghost.reveal volen /\
      Ghost.reveal vclen > 0 /\ Ghost.reveal vclen % 16 = 0
    }
  -> olen: size_t{size_v olen = Ghost.reveal volen}
  -> output:lbuffer uint8 olen
  -> our_identity_pub_key:pubkey_p
  -> their_identity_pub_key:pubkey_p
  -> their_ephemeral_pub_key:pubkey_p
  -> msg_key:key_p
  -> prev_counter:size_t
  -> counter:size_t
  -> clen: size_t{v clen = Ghost.reveal vclen}
  -> ciphertext: lbuffer uint8 clen
  -> tag8:lbuffer uint8 (size 8) ->
  Stack size_t
  (requires (fun h -> live h output /\ live h our_identity_pub_key /\ live h their_identity_pub_key
                 /\ live h msg_key /\ live h their_ephemeral_pub_key /\ live h ciphertext
		 /\ live h tag8
                 /\ disjoint output our_identity_pub_key
                 /\ disjoint output their_identity_pub_key
                 /\ disjoint output msg_key
                 /\ disjoint output their_ephemeral_pub_key
                 /\ disjoint output ciphertext
                 /\ disjoint output tag8))
  (ensures  (fun h0 plen h1 -> modifies1 output h0 h1 /\ v plen <= Ghost.reveal volen /\
    begin
      let expected = decrypt_spec
        h0.[our_identity_pub_key] h0.[their_identity_pub_key] h0.[their_ephemeral_pub_key]
	h0.[msg_key] (v prev_counter) (v counter) h0.[ciphertext] h0.[tag8]
      in decrypt_return_post #volen #vclen expected olen output plen h0 h1
    end
  ))

let decrypt #volen #vclen olen output our_identity_pub_key their_identity_pub_key
  their_ephemeral_pub_key msg_key prev_counter counter clen ciphertext  tag8 =
  (**) let h0 = ST.get () in
  push_frame ();
  let maxwmlen = clen +! (size 57) in
  (**) let h1 = ST.get () in
  [@inline_let]
  let max = (size 96) +! (size 8) in
  let scratch = create max (u8 0) in
  (**) let h2 = ST.get () in
  let keys = sub #MUT #uint8 #max scratch (size 0) (size 96) in
  let computed_tag8 = sub #MUT #uint8 #max scratch (size 96) (size 8) in
  (**) assert(disjoint keys computed_tag8);
  (* Compute the keys *)
  decrypt_compute_keys keys msg_key counter;
  (**) let h3 = ST.get () in
  (**) Seq.eq_intro h3.[keys] (let (expected_keys) = decrypt_compute_keys_spec
  (**)  h0.[msg_key] (v counter) in expected_keys);
  let enc_key = sub keys (size 0) (size 32) in
  let mac_key = sub keys (size 32) (size 32) in
  let enc_iv  = sub keys (size 64) (size 16) in
  (**) assert(disjoint enc_key enc_iv /\ disjoint enc_iv mac_key /\ disjoint enc_key mac_key);
  (* Compute the whisper_msg *)
  let equal_tag = decrypt_serialize_and_compare_tag #volen #vclen olen output computed_tag8
    their_ephemeral_pub_key mac_key our_identity_pub_key their_identity_pub_key prev_counter
    counter clen ciphertext tag8
  in
  (**) let h4 = ST.get () in
  (**) assert(equal_tag = decrypt_serialize_and_compare_tag_spec h0.[their_ephemeral_pub_key]
  (**)   h3.[mac_key] h0.[our_identity_pub_key] h0.[their_identity_pub_key] (v prev_counter)
  (**)   (v counter) h0.[ciphertext] h0.[tag8]);
  let plen : size_t = decrypt_branch_on_bad_tag #volen #vclen olen output equal_tag enc_key enc_iv
    clen ciphertext
  in
  (**) let h5 = ST.get () in
  (**) assert(let expected = decrypt_branch_on_bad_tag_spec equal_tag h3.[enc_key] h3.[enc_iv]
  (**)     h0.[ciphertext]
  (**)   in decrypt_return_post #volen #vclen expected olen output plen h0 h5);
  pop_frame ();
  (**) let h6 = ST.get () in
  (**) assert(let expected = decrypt_branch_on_bad_tag_spec equal_tag h3.[enc_key] h3.[enc_iv]
  (**)      h0.[ciphertext]
  (**)    in decrypt_return_post #volen #vclen expected olen output plen h5 h6);
  (**) assert(let expected = decrypt_spec
  (**)     h0.[our_identity_pub_key] h0.[their_identity_pub_key] h0.[their_ephemeral_pub_key]
  (**)     h0.[msg_key] (v prev_counter) (v counter) h0.[ciphertext] h0.[tag8]
  (**)   in decrypt_return_post #volen #vclen expected olen output plen h0 h6);
  (**) assert(modifies1 output h0 h6);
  plen


val priv_to_pub:
    output: lbuffer uint8 (size 33)
  -> secret: lbuffer uint8 (size 32) ->
  Stack unit
	 (requires (fun h -> live h output /\ live h secret /\ disjoint output secret))
	 (ensures (fun h0 _ h1 -> modifies1 output h0 h1 /\
	   as_seq h1 output == Spec.Signal.Crypto.priv_to_pub (as_seq h0 secret)
	 ))

let priv_to_pub output secret = priv_to_pub output secret


val generate_key_pair:
     e:(Ghost.erased Spec.Signal.Crypto.entropy)
  -> priv:privkey_p
  -> pub:pubkey_p
  -> Stack unit
  (requires (fun h -> live h priv /\ live h pub /\ disjoint priv pub))
  (ensures (fun h0 _ h1 -> modifies2 priv pub h0 h1 /\ begin
      let (expected_priv, expected_pub) = Spec.Signal.Core.generate_key_pair e in
      expected_priv == as_seq h1 priv /\
      expected_pub == as_seq h1 pub
    end
  ))

let generate_key_pair e priv pub =
  random_bytes e (size 32) priv;
  priv_to_pub pub priv
