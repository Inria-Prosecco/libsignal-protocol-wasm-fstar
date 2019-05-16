module Impl.Signal.Messages

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

open Impl.Signal.Crypto

module Seq = Lib.Sequence

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

module ST = FStar.HyperStack.ST

let op_String_Access (#a:Type) (#len:size_t) (h:mem) (b:lbuffer a len) = as_seq h b

inline_for_extraction noextract val concat1:
     #vilen:Ghost.erased size_nat{Ghost.reveal vilen + 1 <= max_size_t}
  -> len:size_t{v len = Ghost.reveal vilen}
  -> output:lbuffer uint8 (len +! size 1)
  -> x:uint8
  -> input:lbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h output /\ live h input /\ disjoint output input))
  (ensures  (fun h0 _ h1 -> modifies1 output h0 h1 /\
    h1.[output] == Spec.Signal.Messages.(( @: )) #(Ghost.reveal vilen) x h0.[input]
  ))

#set-options "--z3rlimit 20"

(**) noextract let lemma_concat1
(**)  (#len:size_nat{len < max_size_t})
(**)  (a:uint8) (b:Spec.Signal.Crypto.lbytes_sub len) : Lemma (
(**)    Spec.Signal.Messages.(( @: )) #len a b == Seq.concat
(**)      (Seq.to_lseq (Seq.create 1 a)) (Seq.to_lseq b)
(**)  ) = ()

inline_for_extraction noextract let concat1 #vilen len output x input =
  (**) let hinit = ST.get () in
  salloc1_trivial hinit (size 1) x (Ghost.hide (loc output))
  (fun _ h1 ->
    (**) live h1 output /\ h1.[output] ==
    (**)    Seq.concat #uint8 #1 #(Ghost.reveal vilen) (Seq.create 1 x) (hinit.[input])
  )
  (fun x1 ->
    let h0 = ST.get () in
    update_sub #MUT #uint8 #(len +. 1ul) output 0ul 1ul x1;
    update_sub #MUT #uint8 #(len +. 1ul) output 1ul len input;
    (**) let h1 = ST.get () in
    (**) Seq.eq_intro (Seq.sub (as_seq h1 output) 0 1) (as_seq h0 x1);
    (**) Seq.lemma_concat2 1 (as_seq h0 x1) (v len) (as_seq h0 input) (as_seq h1 output);
    (**) Seq.eq_intro (as_seq h1 output)
    (**)  (Seq.concat (as_seq #MUT #uint8 #1ul h0 x1)
    (**)  (as_seq #MUT #uint8 #len h0 input))
  );
  (**) lemma_concat1 #(Ghost.reveal vilen) x hinit.[input]

inline_for_extraction noextract val equal_bytes:
    #vlen: Ghost.erased size_nat
  -> len: size_t{v len == Ghost.reveal vlen}
  -> input0: lbuffer uint8 len
  -> input1: lbuffer uint8 len ->
 Stack bool
	 (requires (fun h -> live h input0 /\ live h input1))
	 (ensures (fun h0 b h1 -> modifies0 h0 h1 /\
	   b = Spec.Signal.Messages.equal_bytes h0.[input0] h0.[input1]
	 ))

inline_for_extraction noextract let equal_bytes #vlen len input0 input1 =
  secure_compare #vlen len input0 input1

val serialize_size_get_length: s:size_t -> Tot (l:size_t{v l == Spec.Signal.Messages.serialize_size_get_length (v s)})
let serialize_size_get_length s =
  let size128 : size_t = size 128 in
  let size16384 : size_t = size 16384 in
  let size2097152 : size_t = size 2097152 in
  let size268435456 : size_t = size 268435456 in
  if s <. size128 then size 1 else
  if s <. size16384 then size 2 else
  if s <. size2097152 then size 3 else
  if s <. size268435456 then size 4
  else size 5

let serialize_bytes_get_length (b:size_t{v b + 6 <= max_size_t}) : Tot (l:size_t{v l == Spec.Signal.Messages.serialize_bytes_get_length (v b)}) =
  1ul +! serialize_size_get_length b +! b

#push-options "--z3rlimit 100"

let serialize_whisper_message_get_length
  (prev_counter:size_t)
  (counter:size_t)
  (ciphertext_len:size_t{v ciphertext_len + Spec.Signal.Messages.size_whisper_message_extra_info <= max_size_t})
  : Tot (r:size_t{v r == Spec.Signal.Messages.serialize_whisper_message_get_length (v prev_counter) (v counter) (v ciphertext_len) })
  =
  serialize_bytes_get_length (size Spec.Signal.Crypto.size_pubkey) +!
  1ul +! serialize_size_get_length counter +!
  1ul +! serialize_size_get_length prev_counter +!
  serialize_bytes_get_length ciphertext_len

#pop-options



val serialize_size: s:size_t -> b:lbuffer uint8 (size 5) ->
  Stack (r:size_t{v r <= 5})
  (requires (fun h -> live h b))
  (ensures  (fun h0 r h1 -> modifies1 b h0 h1 /\
    v r = Spec.Signal.Messages.serialize_size_get_length (v s) /\
    Seq.sub h1.[b] 0 (v r) == Spec.Signal.Messages.serialize_size (v s)
  ))

let serialize_size sz b =
  (**) [@ inline_let]
  (**) let expected = Spec.Signal.Messages.serialize_size (v sz) in
  if sz <=. 0x7ful then
   (let x0 = to_u8 sz &. u8 0x7f in
    upd b (size 0) x0;
    (**) let h1 = ST.get () in
    (**) Seq.eq_intro (Seq.sub h1.[b] 0 1) expected;
    size 1)
  else if sz <=. 0x3ffful then
   (let x0 = (to_u8 (sz &. 0x7ful)) |. u8 0x80 in
    let x1 = (to_u8 (sz >>. 7ul)) &. u8 0x7f in
    upd b (size 0) x0;
    upd b (size 1) x1;
    (**) let h1 = ST.get () in
    (**) Seq.eq_intro (Seq.sub h1.[b] 0 2) expected;
    size 2)
  else if sz <=. 0x1ffffful then
   (let x0 = to_u8 (sz &. 0x7ful) |. u8 0x80 in
    let x1 = to_u8 (sz >>. 7ul) |.  u8 0x80 in
    let x2 = to_u8 (sz >>. 14ul) &. u8 0x7f in
    upd b (size 0) x0;
    upd b (size 1) x1;
    upd b (size 2) x2;
    (**) let h1 = ST.get () in
    (**) Seq.eq_intro (Seq.sub h1.[b] 0 3) expected;
    size 3)
  else if sz <=. 0xffffffful then
   (let x0 = to_u8 (sz &. 0x7ful) |. u8 0x80 in
    let x1 = to_u8 (sz >>. 7ul) |. u8 0x80 in
    let x2 = to_u8 (sz >>. 14ul) |. u8 0x80 in
    let x3 = to_u8 (sz >>. 21ul) &. u8 0x7f in
    upd b (size 0) x0;
    upd b (size 1) x1;
    upd b (size 2) x2;
    upd b (size 3) x3;
    (**) let h1 = ST.get () in
    (**) Seq.eq_intro (Seq.sub h1.[b] 0 4) expected;
    size 4)
  else
   (let x0 = to_u8 (sz &. 0x7ful) |. u8 0x80 in
    let x1 = to_u8 (sz >>. 7ul) |. u8 0x80 in
    let x2 = to_u8 (sz >>. 14ul) |. u8 0x80 in
    let x3 = to_u8 (sz >>. 21ul) |. u8 0x80 in
    let x4 = to_u8 (sz >>. 28ul) &. u8 0x7f in
    upd b (size 0) x0;
    upd b (size 1) x1;
    upd b (size 2) x2;
    upd b (size 3) x3;
    upd b (size 4) x4;
    (**) let h1 = ST.get () in
    (**) Seq.eq_intro (Seq.sub h1.[b] 0 5) expected;
    size 5)


#set-options "--z3rlimit 30"

val serialize_varint: b:lbuffer uint8 (size 6) -> s:size_t -> f:uint8 ->
  Stack (l:size_t{v l <= 6})
  (requires (fun h -> live h b))
  (ensures  (fun h0 l h1 -> modifies1 b h0 h1 /\
    v l = Seq.length (Spec.Signal.Messages.serialize_varint (v s) f) /\
    Seq.sub h1.[b] 0 (v l) == Spec.Signal.Messages.serialize_varint (v s) f
  ))

let serialize_varint b s f =
  let sub0 = sub #MUT #uint8 #(size 6) b (size 0) (size 1) in
  (**) let h0 = ST.get () in
  salloc1_trivial h0 (size 5) (u8 0) (Ghost.hide (loc b))
  (**) (fun l h1 -> live h1 b /\ v l <= 6 /\
  (**)  v l = Seq.length (Spec.Signal.Messages.serialize_varint (v s) f) /\
  (**)  Seq.sub h1.[b] 0 (v l) == Spec.Signal.Messages.serialize_varint (v s) f
  (**) )
  (fun sub1 ->
    upd #uint8 #(size 1) sub0 (size 0) (f <<. size 3);
    let l = serialize_size s sub1 in
    concat1 #(Ghost.hide 5) (size 5) b (f <<. size 3) sub1;
    (**) let h1 = ST.get () in
    (**) Seq.eq_intro
    (**)  (Seq.sub h1.[b] 0 (v l + 1))
    (**)  (Seq.to_lseq (Spec.Signal.Messages.serialize_varint (v s) f));
    l +. (size 1)
  )

val serialize_bytes:
     #vilen: (Ghost.erased size_nat){Ghost.reveal vilen + 6 <= max_size_t}
  -> len: size_t{v len = Ghost.reveal vilen}
  -> o:lbuffer uint8 (len +! size 6)
  -> i:lbuffer uint8 len
  -> f:uint8 ->
  Stack (l:size_t{v l <= 6 + Ghost.reveal vilen})
  (requires (fun h -> live h o /\ live h i /\ disjoint o i))
  (ensures  (fun h0 l h1 -> modifies1 o h0 h1 /\
    v l == Spec.Signal.Messages.serialize_bytes_get_length (Ghost.reveal vilen) /\
    Seq.sub h1.[o] 0 (v l) == Spec.Signal.Messages.serialize_bytes h0.[i] f
  ))

#set-options "--z3rlimit 100"

let serialize_bytes #vilen len o i f =
  let max = size 6 +. len in
  push_frame ();
  let b1full = create (size 5) (u8 0) in
  (**) let h0 = ST.get () in
  let b1len = serialize_size len b1full in
  let b1 = sub b1full (size 0) b1len in
  let output0 = sub o (size 0) (size 1) in
  let output1 = sub o (size 1) b1len in
  let output2 = sub o (size 1 +! b1len) len in
  assert(disjoint output0 output1 /\ disjoint output0 output2);
  assert(disjoint output1 output2);
  let b0 = ((f <<. (size 3)) |. (u8 2)) in
  upd #uint8 #(size 1) output0 (size 0) b0;
  copy #MUT #uint8 #b1len output1 b1;
  copy #MUT #uint8 #len output2 i;
  (**) let h1 = ST.get () in
  (**) Seq.eq_intro (Seq.sub h1.[o] 0 1) (Seq.create 1 b0);
  (**) Seq.eq_intro (Seq.sub h1.[o] 1 (size_v b1len))
  (**)   (Spec.Signal.Messages.serialize_size (Ghost.reveal vilen));
  (**) Seq.eq_intro (Seq.sub h1.[o] (1 + size_v b1len) (size_v len)) h0.[i];
  (**) Seq.lemma_concat3
  (**)   1 (Seq.sub h1.[o] 0 1)
  (**)   (v b1len) ((Seq.sub h1.[o] 1 (size_v b1len)))
  (**)   (v len) (Seq.sub h1.[o] (1 + size_v b1len) (v len))
  (**)   (Seq.sub h1.[o] 0 (1 + size_v b1len + size_v len));
  (**) Seq.eq_intro
  (**)   (Seq.sub h1.[o] 0 (1 + size_v b1len + size_v len))
  (**)   (Spec.Signal.Messages.serialize_bytes h0.[i] f);
  pop_frame ();
  (size 1 +! b1len +! len)



#set-options "--z3rlimit 10"

/// Signal Constants

val const_zz: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b Spec.Signal.Messages.zz
}
let const_zz = createL_global Spec.Signal.Messages.zz_list

val const_ff: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b Spec.Signal.Messages.ff
}
let const_ff = createL_global Spec.Signal.Messages.ff_list

val const_fifty_one: b:ilbuffer uint8 1ul{
  recallable b /\ witnessed b Spec.Signal.Messages.fifty_one
}
let const_fifty_one =
  createL_global Spec.Signal.Messages.fifty_one_list

val const_two: b:ilbuffer uint8 (size 1){
  recallable b /\ witnessed b Spec.Signal.Messages.two
}
let const_two = createL_global Spec.Signal.Messages.two_list

val const_one: b:ilbuffer uint8 (size 1){
  recallable b /\ witnessed b Spec.Signal.Messages.one
}
let const_one = createL_global Spec.Signal.Messages.one_list

val const_zero: b:ilbuffer uint8 (size 1){
  recallable b /\ witnessed b Spec.Signal.Messages.zero
}
let const_zero = createL_global Spec.Signal.Messages.zero_list


inline_for_extraction let vsize_label_WhisperMessageKeys : size_t = size 18
val const_label_WhisperMessageKeys: b:ilbuffer uint8 vsize_label_WhisperMessageKeys{
  recallable b /\ witnessed b Spec.Signal.Messages.label_WhisperMessageKeys
}
let const_label_WhisperMessageKeys = createL_global Spec.Signal.Messages.label_WhisperMessageKeys_list

inline_for_extraction let vsize_label_WhisperText : size_t = size 11
val const_label_WhisperText: b:ilbuffer uint8 vsize_label_WhisperText{
  recallable b /\ witnessed b Spec.Signal.Messages.label_WhisperText
}
let const_label_WhisperText = createL_global Spec.Signal.Messages.label_WhisperText_list

inline_for_extraction let vsize_label_WhisperRatchet : size_t = size 14
val const_label_WhisperRatchet: b:ilbuffer uint8 vsize_label_WhisperRatchet{
  recallable b /\ witnessed b Spec.Signal.Messages.label_WhisperRatchet
}
let const_label_WhisperRatchet = createL_global Spec.Signal.Messages.label_WhisperRatchet_list



/// Serializing WhisperMessages


#set-options "--z3rlimit 50"

inline_for_extraction noextract val serialize_whisper_message_aux0:
     #vclen: (Ghost.erased size_nat){Ghost.reveal vclen + 57 <= max_size_t}
  -> clen:size_t{size_v clen = Ghost.reveal vclen}
  -> output:lbuffer uint8 (clen +! size 57)
  -> our_sending_ephemeral_pub_key:pubkey_p ->
  Stack size_t
  (requires (fun h -> live h output /\ live h our_sending_ephemeral_pub_key /\
    disjoint output our_sending_ephemeral_pub_key
  ))
  (ensures  (fun h0 len0 h1 -> modifies1 output h0 h1 /\
    v len0 == Spec.Signal.Messages.serialize_bytes_get_length 33 /\
    Seq.sub h1.[output] 0 (v len0) ==
      Spec.Signal.Messages.serialize_bytes h0.[our_sending_ephemeral_pub_key] (u8 1)
  ))

inline_for_extraction noextract let serialize_whisper_message_aux0 #vclen clen bxfull  our_sending_ephemeral_pub_key =
  let max : size_t = size 57 +. clen in
  let b0full : lbuffer uint8 (size 39) = sub #MUT #uint8 #max bxfull (size 0) (size 39) in
  let len0 : size_t =
    serialize_bytes #(Ghost.hide 33) (size 33) b0full our_sending_ephemeral_pub_key (u8 1)
  in
  len0

inline_for_extraction noextract val serialize_whisper_message_aux1:
     #vclen: (Ghost.erased size_nat){Ghost.reveal vclen + 57 <= max_size_t}
  -> clen:size_t{size_v clen = Ghost.reveal vclen}
  -> output:lbuffer uint8 (clen +! size 57)
  -> our_sending_ephemeral_pub_key:pubkey_p
  -> len0:size_t{v len0 = Spec.Signal.Messages.serialize_bytes_get_length 33}
  -> counter:size_t ->
  Stack size_t
  (requires (fun h -> live h output /\
    Seq.sub h.[output] 0 (v len0) ==
      Spec.Signal.Messages.serialize_bytes h.[our_sending_ephemeral_pub_key] (u8 1)
  ))
  (ensures  (fun h0 len1 h1 -> modifies1 output h0 h1 /\
    v len1 = 1 + Spec.Signal.Messages.serialize_size_get_length (v counter)  /\
    Seq.sub h1.[output] (v len0) (v len1) ==
      Spec.Signal.Messages.serialize_varint (v counter) (u8 2) /\
    Seq.sub h1.[output] 0 (v len0) ==
      Spec.Signal.Messages.serialize_bytes h0.[our_sending_ephemeral_pub_key] (u8 1)
  ))

inline_for_extraction noextract let serialize_whisper_message_aux1 #vclen clen
  bxfull our_sending_ephemeral_pub_key len0 counter =
  let max : size_t = size 57 +. clen in
  let b0 : lbuffer uint8 len0 = sub #MUT #uint8 #max bxfull (size 0) len0 in
  let b1full : lbuffer uint8 (size 6) = sub #MUT #uint8 #max bxfull len0 (size 6) in
  let len1 : size_t = serialize_varint b1full counter (u8 2) in
  (**) assert(disjoint b1full b0);
  len1

inline_for_extraction noextract val serialize_whisper_message_aux2:
    #vclen: (Ghost.erased size_nat){Ghost.reveal vclen + 57 <= max_size_t}
  -> clen:size_t{size_v clen = Ghost.reveal vclen}
  -> output:lbuffer uint8 (clen +! size 57)
  -> our_sending_ephemeral_pub_key:pubkey_p
  -> len0:size_t{v len0 = Spec.Signal.Messages.serialize_bytes_get_length 33}
  -> counter:size_t
  -> len1:size_t{v len1 = 1 + Spec.Signal.Messages.serialize_size_get_length (v counter)}
  -> prev_counter:size_t ->
  Stack size_t
  (requires (fun h -> live h output /\
    Seq.sub h.[output] 0 (v len0) ==
      Spec.Signal.Messages.serialize_bytes h.[our_sending_ephemeral_pub_key] (u8 1) /\
    Seq.sub h.[output] (v len0) (v len1) ==
      Spec.Signal.Messages.serialize_varint (v counter) (u8 2)
  ))
  (ensures  (fun h0 len2 h1 -> modifies1 output h0 h1 /\
    v len2 = 1 + Spec.Signal.Messages.serialize_size_get_length (v prev_counter)  /\
    Seq.sub h1.[output] (v len0 + v len1) (v len2) ==
      Spec.Signal.Messages.serialize_varint (v prev_counter) (u8 3) /\
    Seq.sub h1.[output] (v len0) (v len1) ==
      Spec.Signal.Messages.serialize_varint (v counter) (u8 2) /\
    Seq.sub h1.[output] 0 (v len0) ==
      Spec.Signal.Messages.serialize_bytes h0.[our_sending_ephemeral_pub_key] (u8 1)
  ))

inline_for_extraction noextract let serialize_whisper_message_aux2 #vclen clen
  bxfull our_sending_ephemeral_pub_key len0 counter len1 prev_counter =
  let max : size_t = size 57 +. clen in
  let b0 : lbuffer uint8 len0 = sub #MUT #uint8 #max bxfull (size 0) len0 in
  let b1 : lbuffer uint8 len1 = sub #MUT #uint8 #max bxfull len0 len1 in
  let b2full : lbuffer uint8 (size 6) = sub #MUT #uint8 #max bxfull (len0 +. len1) (size 6) in
  let len2 : size_t = serialize_varint b2full prev_counter (u8 3) in
  (**) assert(disjoint b2full b0);
  (**) assert(disjoint b2full b1);
  len2

inline_for_extraction noextract val serialize_whisper_message_aux3:
    #vclen: (Ghost.erased size_nat){Ghost.reveal vclen + 57 <= max_size_t}
  -> clen:size_t{size_v clen = Ghost.reveal vclen}
  -> output:lbuffer uint8 (clen +! size 57)
  -> our_sending_ephemeral_pub_key:pubkey_p
  -> len0:size_t{v len0 = Spec.Signal.Messages.serialize_bytes_get_length 33}
  -> counter:size_t
  -> len1:size_t{v len1 = 1 + Spec.Signal.Messages.serialize_size_get_length (v counter)}
  -> prev_counter:size_t
  -> len2:size_t{v len2 = 1 + Spec.Signal.Messages.serialize_size_get_length (v prev_counter)}
  -> ciphertext:lbuffer uint8 clen ->
  Stack size_t
  (requires (fun h -> live h output /\ live h ciphertext /\ disjoint ciphertext output /\
    Seq.sub h.[output] 0 (v len0) ==
      Spec.Signal.Messages.serialize_bytes h.[our_sending_ephemeral_pub_key] (u8 1) /\
    Seq.sub h.[output] (v len0) (v len1) ==
      Spec.Signal.Messages.serialize_varint (v counter) (u8 2) /\
    Seq.sub h.[output] (v len0 + v len1) (v len2) ==
      Spec.Signal.Messages.serialize_varint (v prev_counter) (u8 3)
  ))
  (ensures  (fun h0 len3 h1 -> modifies1 output h0 h1 /\
    v len3 = Spec.Signal.Messages.serialize_bytes_get_length (Ghost.reveal vclen)  /\
    Seq.sub h1.[output] (v len0 + v len1 + v len2) (v len3) ==
      Spec.Signal.Messages.serialize_bytes h0.[ciphertext] (u8 4) /\
    Seq.sub h1.[output] (v len0 + v len1) (v len2) ==
      Spec.Signal.Messages.serialize_varint (v prev_counter) (u8 3) /\
    Seq.sub h1.[output] (v len0) (v len1) ==
      Spec.Signal.Messages.serialize_varint (v counter) (u8 2) /\
    Seq.sub h1.[output] 0 (v len0) ==
      Spec.Signal.Messages.serialize_bytes h0.[our_sending_ephemeral_pub_key] (u8 1)
  ))

#reset-options "--z3refresh --z3rlimit 100 --max_fuel 0 --initial_fuel 0 --max_ifuel 0 --initial_ifuel 0"

noextract let lemma_add3
  (x0:size_t)
  (x1:size_t{v x0 + v x1 <= max_size_t})
  (x2:size_t{v x0 + v x1 + v x2 <= max_size_t}) : Lemma (ensures (
    v (x0 +. x1 +. x2) = v x0 + v x1 + v x2
  )) = ()

inline_for_extraction noextract let serialize_whisper_message_aux3 #vclen clen
  bxfull our_sending_ephemeral_pub_key len0 counter len1 prev_counter len2 ciphertext =
  let max : size_t = size 57 +! clen in
  lemma_add3 len0 len1 len2;
  let offset : size_t = len0 +! len1 +! len2 in
  let bbefore : lbuffer uint8 offset = sub #MUT #uint8 #max bxfull (size 0) offset in
  let b3full : lbuffer uint8 (clen +! size 6) =
    sub #MUT #uint8 #max bxfull offset (clen +! size 6)
  in
  (**) assert(disjoint b3full ciphertext);
  let len3 : size_t = serialize_bytes #vclen clen b3full ciphertext (u8 4) in
  (**) assert(disjoint b3full bbefore);
  len3

#set-options "--z3rlimit 50"

noextract let lemma_add4
  (x0:size_t)
  (x1:size_t{v x0 + v x1 <= max_size_t})
  (x2:size_t{v x0 + v x1 + v x2 <= max_size_t})
  (x3:size_t{v x0 + v x1 + v x2 + v x3 <= max_size_t}): Lemma (ensures (
    v (x0 +. x1 +. x2 +. x3) = v x0 + v x1 + v x2 + v x3
  )) = ()


inline_for_extraction noextract val serialize_whisper_message:
     #vclen: (Ghost.erased size_nat){Ghost.reveal vclen + 57 <= max_size_t}
  -> clen:size_t{size_v clen = Ghost.reveal vclen}
  -> output:lbuffer uint8 (clen +! size 57)
  -> our_sending_ephemeral_pub_key:pubkey_p
  -> prev_counter:size_t
  -> counter:size_t
  -> ciphertext:lbuffer uint8 clen ->
  Stack size_t
  (requires (fun h -> live h output /\ live h our_sending_ephemeral_pub_key /\ live h ciphertext
		 /\ disjoint output our_sending_ephemeral_pub_key
                 /\ disjoint output ciphertext
  ))
  (ensures  (fun h0 len h1 -> modifies1 output h0 h1 /\ begin
    let expected = Spec.Signal.Messages.serialize_whisper_message
	h0.[our_sending_ephemeral_pub_key]
	(v prev_counter) (v counter)
	h0.[ciphertext]
    in
    v len = Spec.Signal.Messages.serialize_whisper_message_get_length
      (v prev_counter) (v counter) (v clen) /\
    Seq.sub h1.[output] 0 (v len) == expected
    end
  ))

val lemma_concat4_right:
    #a:Type0
  -> len0:size_nat
  -> s0:Lib.Sequence.lseq a len0
  -> len1:size_nat{len0 + len1 <= max_size_t}
  -> s1:Lib.Sequence.lseq a len1
  -> len2:size_nat{len0 + len1 + len2 <= max_size_t}
  -> s2:Lib.Sequence.lseq a len2
  -> len3:size_nat{len0 + len1 + len2 + len3 <= max_size_t}
  -> s3:Lib.Sequence.lseq a len3
  -> s:Lib.Sequence.lseq a (len0 + len1 + len2 + len3) ->
  Lemma
    (requires
      Lib.Sequence.sub s 0 len0 == s0 /\
      Lib.Sequence.sub s len0 len1 == s1 /\
      Lib.Sequence.sub s (len0 + len1) len2 == s2 /\
      Lib.Sequence.sub s (len0 + len1 + len2) len3 == s3)
    (ensures s == Lib.Sequence.concat s0 (Lib.Sequence.concat s1 (Lib.Sequence.concat s2 s3)))

let lemma_concat4_right #a len0 s0 len1 s1 len2 s2 len3 s3 s =
  let s' = Lib.Sequence.concat s0 (Lib.Sequence.concat s1 (Lib.Sequence.concat s2 s3)) in
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s (len0 + len1) (len2 + len3)) len2;
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s' (len0 + len1) (len2 + len3)) len2;
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s len0 (len1 + len2 + len3)) len1;
  FStar.Seq.Properties.lemma_split (Lib.Sequence.sub s' len0 (len1 + len2 + len3)) len1;
  FStar.Seq.Properties.lemma_split s len0;
  FStar.Seq.Properties.lemma_split s' len0

inline_for_extraction noextract let serialize_whisper_message #vclen clen output
  our_sending_ephemeral_pub_key prev_counter counter ciphertext =
  (**) let h0 = ST.get () in
  let max : size_t = size 57 +. clen in
  let len0 : size_t =
    serialize_whisper_message_aux0 #vclen clen output our_sending_ephemeral_pub_key
  in
  let len1 : size_t =
    serialize_whisper_message_aux1 #vclen clen output our_sending_ephemeral_pub_key
    len0 counter
  in
  let len2 : size_t =
    serialize_whisper_message_aux2 #vclen clen output our_sending_ephemeral_pub_key
    len0 counter len1 prev_counter
  in
  let len3 : size_t =
    serialize_whisper_message_aux3 #vclen clen
    output our_sending_ephemeral_pub_key len0 counter len1 prev_counter len2 ciphertext
  in
  (**) lemma_add4 len0 len1 len2 len3;
  (**) let h1 = ST.get () in
  (**) lemma_concat4_right #uint8
  (**)  (v len0) (Seq.sub h1.[output] 0 (v len0))
  (**)  (v len1) (Seq.sub h1.[output] (v len0) (v len1))
  (**)  (v len2) (Seq.sub h1.[output] (v len0 + v len1) (v len2))
  (**)  (v len3) (Seq.sub h1.[output] (v len0 + v len1 + v len2) (v len3))
  (**)  (Seq.sub h1.[output] 0 (v len0 + v len1 + v len2 + v len3));
  (**) Seq.eq_intro
  (**)   (Seq.sub h1.[output] 0 (v len0 + v len1 + v len2 + v len3))
  (**)   (Spec.Signal.Messages.serialize_whisper_message
  (**)	    h0.[our_sending_ephemeral_pub_key]
  (**)	    (v prev_counter) (v counter)
  (**)	    h0.[ciphertext]);
  (len0 +. len1 +. len2 +. len3)

(* BB. Aliasing for now... *)
let whisper_message #vclen clen output our_sending_ephemeral_pub_key prev_counter counter ciphertext  =
  serialize_whisper_message #vclen clen output our_sending_ephemeral_pub_key prev_counter counter ciphertext

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 150"


val mac_whisper_msg:
    #vilen: (Ghost.erased size_nat){Ghost.reveal vilen + 32 +
      (* we need an extra 32 bits for scratch memory *)
      Spec.Signal.Messages.size_mac_whisper_msg_extra_info +
      (* the next constant added is needed for hmac *)
      Spec.Hash.Definitions.block_length (Spec.Hash.Definitions.SHA2_256) < max_size_t}
  -> tag:lbuffer uint8 (size 8)
  -> mac_key: key_p
  -> send_identity_pub_key:pubkey_p
  -> recv_identity_pub_key:pubkey_p
  -> len: size_t{v len = Ghost.reveal vilen}
  -> whisper_msg:lbuffer uint8 len ->
  Stack unit
  (requires (fun h -> live h tag /\ live h mac_key /\ live h send_identity_pub_key
		 /\ live h recv_identity_pub_key /\ live h whisper_msg
                 /\ disjoint tag mac_key
                 /\ disjoint tag send_identity_pub_key
                 /\ disjoint tag recv_identity_pub_key
                 /\ disjoint tag whisper_msg))
  (ensures  (fun h0 _ h1 -> modifies1 tag h0 h1 /\
    h1.[tag] == Spec.Signal.Messages.mac_whisper_msg
      h1.[mac_key] h1.[send_identity_pub_key] h1.[recv_identity_pub_key] h1.[whisper_msg]
  ))

let mac_whisper_msg #vilen tag mac_key send_identity_pub_key recv_identity_pub_key len whisper_msg =
  let max = (size 32) +. (size 33) +. (size 33) +. (size 1) +. len in
  push_frame ();
  let scratch = create max (u8 0) in
  (**) let h0 = ST.get() in
  let tagfull = sub #MUT #uint8 #max scratch (size 0) (size 32) in
  let mac_input = sub #MUT #uint8 #max scratch (size 32) (size 67 +. len) in
  let mac_input1 = sub mac_input (size 0) (size 33) in
  let mac_input2 = sub mac_input (size 33) (size 33) in
  let mac_input3 = sub mac_input (size 66) (size 1) in
  let mac_input4 = sub mac_input (size 67) len in
  copy #MUT #uint8 #(size 33) mac_input1 recv_identity_pub_key;
  copy #MUT #uint8 #(size 33) mac_input2 send_identity_pub_key;
  (**) recall_contents #uint8 #(size 1) const_fifty_one (Spec.Signal.Messages.fifty_one);
  copy #IMMUT #uint8 #(size 1) mac_input3 const_fifty_one;
  copy #MUT #uint8 #len mac_input4 whisper_msg;
  (**) let h1 = ST.get() in
  (**) assert(Seq.sub h1.[mac_input] 66 1 == Spec.Signal.Messages.fifty_one);
  (**) lemma_concat4_right
  (**)   33 h0.[recv_identity_pub_key] 33 h0.[send_identity_pub_key]
  (**)   1 (Spec.Signal.Messages.fifty_one) (v len) h0.[whisper_msg]
  (**)   h1.[mac_input];
  hmac_mut #(Ghost.hide (67 + Ghost.reveal vilen))
    tagfull mac_key ((size 33) +. (size 33) +. (size 1) +. len) mac_input;
  let tag8 = sub #MUT #uint8 #(size 32) tagfull (size 0) (size 8) in
  copy tag tag8;
  (**) let h2 = ST.get () in
  (**) Seq.eq_intro h2.[mac_input] (Seq.concat (Seq.concat (Seq.concat
  (**)   h2.[recv_identity_pub_key] h2.[send_identity_pub_key])
  (**)   (Spec.Signal.Messages.fifty_one)) h2.[whisper_msg]);
  (**) Seq.eq_intro h2.[tag] (Seq.sub (Spec.Signal.Crypto.hmac h2.[mac_key]
  (**)   (Seq.concat (Seq.concat (Seq.concat
  (**)     h2.[recv_identity_pub_key] h2.[send_identity_pub_key])
  (**)     (as_seq #IMMUT #uint8 #(size 1) h2 const_fifty_one)) h2.[whisper_msg])) 0 8);
  (**) Seq.eq_intro
  (**)   (Seq.sub (Spec.Signal.Crypto.hmac h2.[mac_key]
  (**)     Seq.((as_seq h2 recv_identity_pub_key) @| (as_seq h2 send_identity_pub_key) @|
  (**)       (as_seq #IMMUT #uint8 #(size 1) h2 const_fifty_one) @| (as_seq h2 whisper_msg))
  (**)   ) 0 8)
  (**)   (Spec.Signal.Messages.mac_whisper_msg
  (**)       h2.[mac_key] h2.[send_identity_pub_key]
  (**)       h2.[recv_identity_pub_key] h2.[whisper_msg]
  (**)     );
  pop_frame ()
