module Test.Impl.Signal

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer

module TS = Test.Spec.Signal

#set-options "--max_fuel 0 --max_ifuel 0"

val t0_input_ourEphemeralPrivKey : b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t0_input_ourEphemeralPrivKey
}
let t0_input_ourEphemeralPrivKey = createL_global TS.t0_input_ourEphemeralPrivKey_list

val t0_input_theirEphemeralPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t0_input_theirEphemeralPubKey
}
let t0_input_theirEphemeralPubKey =
  createL_global TS.t0_input_theirEphemeralPubKey_list

val t0_input_rootKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t0_input_rootKey
}
let t0_input_rootKey =
  createL_global TS.t0_input_rootKey_list

val t0_output_rootKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t0_output_rootKey
}
let t0_output_rootKey =
  createL_global TS.t0_output_rootKey_list

val t0_output_chainKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t0_output_chainKey
}
let t0_output_chainKey =
  createL_global TS.t0_output_chainKey_list

val  t1_input_ourIdentityPrivKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t1_input_ourIdentityPrivKey
}
let t1_input_ourIdentityPrivKey =
  createL_global TS.t1_input_ourIdentityPrivKey_list

val  t1_input_basePrivKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t1_input_basePrivKey
}
let t1_input_basePrivKey =
  createL_global TS.t1_input_basePrivKey_list

val  t1_input_ourOneTimePrivKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t1_input_ourOneTimePrivKey
}
let t1_input_ourOneTimePrivKey =
  createL_global TS.t1_input_ourOneTimePrivKey_list

val  t1_input_theirIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t1_input_theirIdentityPubKey
}
let t1_input_theirIdentityPubKey =
  createL_global TS.t1_input_theirIdentityPubKey_list

val  t1_input_theirSignedPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t1_input_theirSignedPubKey
}
let t1_input_theirSignedPubKey =
  createL_global TS.t1_input_theirSignedPubKey_list

val  t1_input_theirOneTimePubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t1_input_theirOneTimePubKey
}
let t1_input_theirOneTimePubKey =
  createL_global TS.t1_input_theirOneTimePubKey_list

val  t1_output_rootKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t1_output_rootKey
}
let t1_output_rootKey =
  createL_global TS.t1_output_rootKey_list

val  t1_output_chainKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t1_output_chainKey
}
let t1_output_chainKey =
  createL_global TS.t1_output_chainKey_list

val t2_input_ourIdentityPrivKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t2_input_ourIdentityPrivKey
}
let t2_input_ourIdentityPrivKey =
  createL_global TS.t2_input_ourIdentityPrivKey_list

val t2_input_ourSignedPrivKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t2_input_ourSignedPrivKey
}
let t2_input_ourSignedPrivKey =
  createL_global TS.t2_input_ourSignedPrivKey_list

val t2_input_ourEphemeralPrivKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t2_input_ourEphemeralPrivKey
}
let t2_input_ourEphemeralPrivKey =
  createL_global TS.t2_input_ourEphemeralPrivKey_list

val t2_input_theirIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t2_input_theirIdentityPubKey
}
let t2_input_theirIdentityPubKey =
  createL_global TS.t2_input_theirIdentityPubKey_list

val t2_input_theirOneTimePubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t2_input_theirOneTimePubKey
}
let t2_input_theirOneTimePubKey =
  createL_global TS.t2_input_theirOneTimePubKey_list

val t2_output_rootKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t2_output_rootKey
}
let t2_output_rootKey =
  createL_global TS.t2_output_rootKey_list

val t3_input_ourIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t3_input_ourIdentityPubKey
}
let t3_input_ourIdentityPubKey =
  createL_global TS.t3_input_ourIdentityPubKey_list

val t3_input_theirIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t3_input_theirIdentityPubKey
}
let t3_input_theirIdentityPubKey =
  createL_global TS.t3_input_theirIdentityPubKey_list

val t3_input_msgKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t3_input_msgKey
}
let t3_input_msgKey =
  createL_global TS.t3_input_msgKey_list

val t3_input_ourEphemeralPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t3_input_ourEphemeralPubKey
}
let t3_input_ourEphemeralPubKey =
  createL_global TS.t3_input_ourEphemeralPubKey_list

val t3_input_msg: b:ilbuffer uint8 (size 159){
  recallable b /\ witnessed b TS.t3_input_msg
}
let t3_input_msg =
  createL_global TS.t3_input_msg_list

let t3_input_previousCounter : size_t = size TS.t3_input_previousCounter

let t3_input_counter : size_t = size TS.t3_input_counter

#set-options "--z3rlimit 20"

val t3_output_result: b:ilbuffer uint8 (size 211){
  recallable b /\ witnessed b TS.t3_output_result
}
let t3_output_result =
  createL_global TS.t3_output_result_list

val t4_input_ourIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t4_input_ourIdentityPubKey
}
let t4_input_ourIdentityPubKey =
  createL_global TS.t4_input_ourIdentityPubKey_list

val t4_input_theirIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t4_input_theirIdentityPubKey
}
let t4_input_theirIdentityPubKey =
  createL_global TS.t4_input_theirIdentityPubKey_list

val t4_input_msgKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t4_input_msgKey
}
let t4_input_msgKey =
  createL_global TS.t4_input_msgKey_list

val t4_input_ourEphemeralPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t4_input_ourEphemeralPubKey
}
let t4_input_ourEphemeralPubKey =
  createL_global TS.t4_input_ourEphemeralPubKey_list

val t4_input_msg: b:ilbuffer uint8 (size 159){
  recallable b /\ witnessed b TS.t4_input_msg
}
let t4_input_msg =
  createL_global TS.t4_input_msg_list

let t4_input_previousCounter : size_t = size TS.t4_input_previousCounter

let t4_input_counter : size_t = size TS.t4_input_counter


val t4_output_result: b:ilbuffer uint8 (size 211){
  recallable b /\ witnessed b TS.t4_output_result
}
let t4_output_result =
  createL_global TS.t4_output_result_list


val t5_input_ourIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t5_input_ourIdentityPubKey
}
let t5_input_ourIdentityPubKey =
  createL_global TS.t5_input_ourIdentityPubKey_list

val t5_input_theirIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t5_input_theirIdentityPubKey
}
let t5_input_theirIdentityPubKey =
  createL_global TS.t5_input_theirIdentityPubKey_list

val t5_input_remoteEphemeralKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t5_input_remoteEphemeralKey
}
let t5_input_remoteEphemeralKey =
  createL_global TS.t5_input_remoteEphemeralKey_list

val t5_input_messageKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t5_input_messageKey
}
let t5_input_messageKey =
  createL_global TS.t5_input_messageKey_list

let t5_input_previousCounter : size_t = size TS.t5_input_previousCounter

let t5_input_counter : size_t = size TS.t5_input_counter

val t5_input_ciphertext: b:ilbuffer uint8 (size 160){
  recallable b /\ witnessed b TS.t5_input_ciphertext
}
let t5_input_ciphertext =
  createL_global TS.t5_input_ciphertext_list

val t5_input_macTag: b:ilbuffer uint8 (size 8){
  recallable b /\ witnessed b TS.t5_input_macTag
}
let t5_input_macTag =
  createL_global TS.t5_input_macTag_list

val t5_output_plaintext: b:ilbuffer uint8 (size 159){
  recallable b /\ witnessed b TS.t5_output_plaintext
}
let t5_output_plaintext =
  createL_global TS.t5_output_plaintext_list

val t6_input_ourIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t6_input_ourIdentityPubKey
}
let t6_input_ourIdentityPubKey =
  createL_global TS.t6_input_ourIdentityPubKey_list

val t6_input_theirIdentityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t6_input_theirIdentityPubKey
}
let t6_input_theirIdentityPubKey =
  createL_global TS.t6_input_theirIdentityPubKey_list

val t6_input_remoteEphemeralKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t6_input_remoteEphemeralKey
}
let t6_input_remoteEphemeralKey =
  createL_global TS.t6_input_remoteEphemeralKey_list

val t6_input_messageKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t6_input_messageKey
}
let t6_input_messageKey =
  createL_global TS.t6_input_messageKey_list

let t6_input_previousCounter : size_t = size TS.t6_input_previousCounter

let t6_input_counter : size_t = size TS.t6_input_counter

val t6_input_ciphertext: b:ilbuffer uint8 (size 160){
  recallable b /\ witnessed b TS.t6_input_ciphertext
}
let t6_input_ciphertext =
  createL_global TS.t6_input_ciphertext_list

val t6_input_macTag: b:ilbuffer uint8 (size 8){
  recallable b /\ witnessed b TS.t6_input_macTag
}
let t6_input_macTag =
  createL_global TS.t6_input_macTag_list

val t6_output_plaintext: b:ilbuffer uint8 (size 159){
  recallable b /\ witnessed b TS.t6_output_plaintext
}
let t6_output_plaintext =
  createL_global TS.t6_output_plaintext_list

val t7_input_identityPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t7_input_identityPubKey
}
let t7_input_identityPubKey =
  createL_global TS.t7_input_identityPubKey_list

val t7_input_signedPubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t7_input_signedPubKey
}
let t7_input_signedPubKey =
  createL_global TS.t7_input_signedPubKey_list

val t7_input_signature: b:ilbuffer uint8 (size 64){
  recallable b /\ witnessed b TS.t7_input_signature
}
let t7_input_signature =
  createL_global TS.t7_input_signature_list


val t8_input_pubKey: b:ilbuffer uint8 (size 33){
  recallable b /\ witnessed b TS.t8_input_pubKey
}
let t8_input_pubKey =
  createL_global TS.t8_input_pubKey_list

val t8_input_privKey: b:ilbuffer uint8 (size 32){
  recallable b /\ witnessed b TS.t8_input_privKey
}
let t8_input_privKey =
  createL_global TS.t8_input_privKey_list

val t8_output_signature: b:ilbuffer uint8 (size 64){
  recallable b /\ witnessed b TS.t8_output_signature
}
let t8_output_signature =
  createL_global TS.t8_output_signature_list


#set-options "--admit_smt_queries true"

let main () =
  C.String.print (C.String.of_literal "TEST 0: (Impl.Signal.Core.ratchet)\n");
  let t0_computed_rootKey = create (size 32) (u8 0) in
  let t0_computed_chainKey = create (size 32) (u8 0) in
  Impl.Signal.Core.ratchet
    t0_computed_rootKey
    t0_computed_chainKey
    t0_input_rootKey
    t0_input_ourEphemeralPrivKey
    t0_input_theirEphemeralPubKey;
  TestLib.compare_and_print (C.String.of_literal "0a. rootKey")
    t0_output_rootKey t0_computed_rootKey (size 32);
  TestLib.compare_and_print (C.String.of_literal "0b. chainKey")
    t0_output_chainKey t0_computed_chainKey (size 32);
  C.String.print (C.String.of_literal "\n\nTEST 1: (Impl.Signal.Core.initiate)\n");
  let t1_computed_rootKey = create (size 32) (u8 0) in
  let t1_computed_chainKey = create (size 32) (u8 0) in
  Impl.Signal.Core.initiate
    t1_computed_rootKey
    t1_computed_chainKey
    t1_input_ourIdentityPrivKey
    t1_input_basePrivKey
    t1_input_ourOneTimePrivKey
    t1_input_theirIdentityPubKey
    t1_input_theirSignedPubKey
    t1_input_theirOneTimePubKey
    true;
  TestLib.compare_and_print (C.String.of_literal "1a. rootKey")
    t1_output_rootKey t1_computed_rootKey (size 32);
  TestLib.compare_and_print (C.String.of_literal "1b. chainKey")
    t1_output_chainKey t1_computed_chainKey (size 32);

  C.String.print (C.String.of_literal "\n\nTEST 2: (Impl.Signal.Core.respond)\n");
  let t2_computed_rootKey = create (size 32) (u8 0) in
  Impl.Signal.Core.respond
    t2_computed_rootKey
    t2_input_ourIdentityPrivKey
    t2_input_ourSignedPrivKey
    t2_input_ourEphemeralPrivKey
    true
    t2_input_theirIdentityPubKey
    t2_input_theirOneTimePubKey;
  TestLib.compare_and_print (C.String.of_literal "2. rootKey")
    t2_output_rootKey t2_computed_rootKey (size 32);

   C.String.print (C.String.of_literal "\n\nTEST 3: (Impl.Signal.Core.encrypt)\n");
   let t3_computed_result = create (size 241) (u8 0) in
   let t3_computed_chainKey = create (size 32) (u8 0) in
   let size_encrypt = Impl.Signal.Core.encrypt
     #(Ghost.hide 159)
     (size 241)
     t3_computed_result
     t3_input_ourIdentityPubKey
     t3_input_theirIdentityPubKey
     t3_input_msgKey
     t3_input_ourEphemeralPubKey
     t3_input_previousCounter
     t3_input_counter
     (size 159)
     t3_input_msg
  in

  TestLib.compare_and_print (C.String.of_literal "3. Ciphertext")
    t3_output_result t3_computed_result size_encrypt;

  C.String.print (C.String.of_literal "\n\nTEST 4: (Impl.Signal.Core.encrypt)\n");
  let t4_computed_result = create (size 241) (u8 0) in
  let t4_computed_chainKey = create (size 32) (u8 0) in
  let size_encrypt = Impl.Signal.Core.encrypt
    #(Ghost.hide 159)
    (size 241)
    t4_computed_result
    t4_input_ourIdentityPubKey
    t4_input_theirIdentityPubKey
    t4_input_msgKey
    t4_input_ourEphemeralPubKey
    t4_input_previousCounter
    t4_input_counter
    (size 159)
    t4_input_msg
  in

  TestLib.compare_and_print (C.String.of_literal "4. Ciphertext")
    t4_output_result t4_computed_result size_encrypt;


  C.String.print (C.String.of_literal "\n\nTEST 5: (Impl.Signal.Core.decrypt)\n");
  let t5_computed_result = create (size 241) (u8 0) in
  let plain_len = Impl.Signal.Core.decrypt
    #(Ghost.hide 241)
    #(Ghost.hide 160)
    (size 241)
    t5_computed_result
    t5_input_ourIdentityPubKey
    t5_input_theirIdentityPubKey
    t5_input_remoteEphemeralKey
    t5_input_messageKey
    t5_input_previousCounter
    t5_input_counter
    (size 160)
    t5_input_ciphertext
    t5_input_macTag
  in

  TestLib.compare_and_print (C.String.of_literal "5. plaintext")
    t5_output_plaintext t5_computed_result plain_len;

  C.String.print (C.String.of_literal "\n\nTEST 6: (Impl.Signal.Core.decrypt)\n");
  let t6_computed_result = create (size 241) (u8 0) in
  let plain_len = Impl.Signal.Core.decrypt
    #(Ghost.hide 241)
    #(Ghost.hide 160)
    (size 241)
    t6_computed_result
    t6_input_ourIdentityPubKey
    t6_input_theirIdentityPubKey
    t6_input_remoteEphemeralKey
    t6_input_messageKey
    t6_input_previousCounter
    t6_input_counter
    (size 160)
    t6_input_ciphertext
    t6_input_macTag
  in
  TestLib.compare_and_print (C.String.of_literal "6. plaintext")
    t6_output_plaintext t6_computed_result (size 64);

  C.String.print (C.String.of_literal "\n\nTEST 7: (Impl.Signal.Core.verify_sig)\n");
  let t7_computed_result = Impl.Signal.Core.verify_sig
    t7_input_identityPubKey
    t7_input_signedPubKey
    t7_input_signature
  in
  begin if t7_computed_result then
    C.String.print (C.String.of_literal "Success !\n")
  else
   C.String.print (C.String.of_literal "Failure !\n")
  end;

  C.String.print (C.String.of_literal "\n\nTEST 8: (Impl.Signal.Core.sign)\n");
  let t8_computed_signature = create (size 64) (u8 0) in
  Impl.Signal.Core.sign
    t8_computed_signature
    t8_input_privKey
    t8_input_pubKey;
  TestLib.compare_and_print (C.String.of_literal "8. signature")
    t8_output_signature t8_computed_signature (size 64);

  C.EXIT_SUCCESS

#set-options "--admit_smt_queries false"
