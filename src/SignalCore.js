(function() {
    'use strict';

    const checkIfInitialized = async function() {
      return new Promise((res,rej) => {
        return res();
      })
    };
    
    async function SignalCoreVerifySig(identityKey,signedPublicKey,signature) {
      await Internal.crypto.Ed25519Verify(
        identityKey,
        signedPublicKey,
        signature
      );
    }

    async function SignalCoreSign(privKey, pubKey) {
      let signature = await Internal.crypto.Ed25519Sign(privKey, pubKey);
      return signature;
    }

    function SignalCoreGenerateRegistrationId() {
      var registrationId = new Uint16Array(Internal.crypto.getRandomBytes(2))[0];
      return registrationId & 0x3fff;
    }

    async function SignalCoreCreateKeyPair(privKey) {
      if (privKey === undefined) {
          privKey = Internal.crypto.getRandomBytes(32);
      }
      return Internal.Curve.async.createKeyPair(privKey);
    }


    async function SignalCoreRatchet(
      rootKey,
      ourEphemeralPrivKey,
      theirEphemeralPubKey
    ) {
      var sharedSecret = await Internal.crypto.ECDHE(
        theirEphemeralPubKey, util.toArrayBuffer(ourEphemeralPrivKey)
      );
      var masterKey = await Internal.HKDF(
        sharedSecret, util.toArrayBuffer(rootKey), "WhisperRatchet"
      );
      // newRootKey, newChainKey
      return [masterKey[0], masterKey[1]];
    }

    async function SignalCoreInitiate(
      ourIdentityPrivKey,
      basePrivKey,
      ourOneTimePrivKey,
      theirIdentityPubKey,
      theirSignedPubKey,
      theirOneTimePubKey,
      definedTheirOnetimePubKey
    ) {
      var sharedSecret;

      if (!definedTheirOnetimePubKey) {
        sharedSecret = new Uint8Array(32 * 4);
      } else {
        sharedSecret = new Uint8Array(32 * 5);
      }

      for (var i = 0; i < 32; i++) {
        sharedSecret[i] = 0xff;
      }
      var ecRes = [
        await Internal.crypto.ECDHE(theirSignedPubKey, ourIdentityPrivKey),
        await Internal.crypto.ECDHE(theirIdentityPubKey, basePrivKey),
        await Internal.crypto.ECDHE(theirSignedPubKey, basePrivKey)
      ]

      sharedSecret.set(new Uint8Array(ecRes[0]), 32);
      sharedSecret.set(new Uint8Array(ecRes[1]), 32 * 2);
      sharedSecret.set(new Uint8Array(ecRes[2]), 32 * 3);

      if (definedTheirOnetimePubKey) {
        var ecRes4 = await Internal.crypto.ECDHE(
          theirOneTimePubKey, basePrivKey
        );
        sharedSecret.set(new Uint8Array(ecRes4), 32 * 4);
      }
      var masterKey = await Internal.HKDF(sharedSecret.buffer, new ArrayBuffer(32), "WhisperText");
      // If we're initiating we go ahead and set our first sending ephemeral key now,
      // otherwise we figure it out when we first maybeStepRatchet with the remote's ephemeral key
      return await SignalCoreRatchet(masterKey[0], ourOneTimePrivKey, theirSignedPubKey);
    }

    async function SignalCoreRespond(
      ourIdentityPrivKey,
      ourSignedPrivKey,
      ourOnetimePrivKey,
      definedOurOnetimePrivKey,
      theirIdentityPubKey,
      theirOnetimePubKey
    ) {
      var sharedSecret;
      if (!definedOurOnetimePrivKey) {
        sharedSecret = new Uint8Array(32 * 4);
      } else {
        sharedSecret = new Uint8Array(32 * 5);
      }

      for (var i = 0; i < 32; i++) {
        sharedSecret[i] = 0xff;
      }

      var ecRes = [
        await Internal.crypto.ECDHE(theirOnetimePubKey, ourIdentityPrivKey),
        await Internal.crypto.ECDHE(theirIdentityPubKey, ourSignedPrivKey),
        await Internal.crypto.ECDHE(theirOnetimePubKey, ourSignedPrivKey)
      ]

      sharedSecret.set(new Uint8Array(ecRes[0]), 32 * 2);
      sharedSecret.set(new Uint8Array(ecRes[1]), 32);
      sharedSecret.set(new Uint8Array(ecRes[2]), 32 * 3);

      if (definedOurOnetimePrivKey) {
        var ecRes4 = await Internal.crypto.ECDHE(
          theirOnetimePubKey, ourOnetimePrivKey
        );
        sharedSecret.set(new Uint8Array(ecRes4), 32 * 4);
      }
      var masterKey = await Internal.HKDF(sharedSecret.buffer, new ArrayBuffer(32), "WhisperText");
      // return RootKey
      return masterKey[0];

      // If we're initiating we go ahead and set our first sending ephemeral key now,
      // otherwise we figure it out when we first maybeStepRatchet with the remote's ephemeral key
    }

    async function SignalCoreFillMessagesKeys(chainKey) {
      var byteArray = new Uint8Array(1);
      byteArray[0] = 1;
      var new_msg_key = await Internal.crypto.sign(chainKey, byteArray.buffer);
      byteArray[0] = 2;
      var new_chain_key = await Internal.crypto.sign(chainKey, byteArray.buffer);

      // return msg_key, new_chain_key
      return [new_msg_key, new_chain_key]
    }

    async function SignalCoreEncrypt(
      ourIdentityPubKey,
      theirIdentityPubKey,
      msgKey,
      ourEphemeralPubKey,
      previousCounter,
      counter,
      buffer,
    ) {
      var msg = new Internal.protobuf.WhisperMessage();
      msg.ephemeralKey = ourEphemeralPubKey;
      var cipherlen = Math.ceil((buffer.byteLength +1)/ 16) * 16;
      msg.ciphertext = new ArrayBuffer(cipherlen);
      var HKDFArg = msgKey;
      var keys = await Internal.HKDF(
        HKDFArg,
          new ArrayBuffer(32), "WhisperMessageKeys");
      msg.counter = counter;
      msg.previousCounter = previousCounter;
      var ciphertext = await Internal.crypto.encrypt(
        keys[0], buffer, keys[2].slice(0, 16)
      );
      msg.ciphertext = ciphertext;
      msg.macKey = keys[1];
      var encodedMsg = msg.toArrayBuffer();
      var result = new ArrayBuffer(encodedMsg.byteLength + 9);
      var macInput = new Uint8Array(encodedMsg.byteLength + 33 * 2 + 1);
      macInput.set(new Uint8Array(ourIdentityPubKey));
      macInput.set(new Uint8Array(theirIdentityPubKey), 33);
      macInput[33 * 2] = (3 << 4) | 3;
      macInput.set(new Uint8Array(encodedMsg), 33 * 2 + 1);
      var mac = await Internal.crypto.sign(msg.macKey, macInput.buffer);
      (new Uint8Array(result))[0] = (3 << 4) | 3;
      (new Uint8Array(result)).set(new Uint8Array(encodedMsg), 1);
      (new Uint8Array(result)).set(new Uint8Array(mac, 0, 8), encodedMsg.byteLength + 1);
      return result;
    }

    async function SignalCoreDecrypt(
      ourIdentityPubKey,
      theirIdentityPubKey,
      remoteEphemeralKey,
      messageKey,
      previousCounter,
      counter,
      ciphertext,
      tag8,
    ) {
      var msg = new Internal.protobuf.WhisperMessage();
      msg.ephemeralKey = remoteEphemeralKey;
      msg.ciphertext = ciphertext;
      msg.counter = counter;
      msg.previousCounter = previousCounter;
      var encodedMsg = msg.toArrayBuffer();
      var macInput = new Uint8Array(encodedMsg.byteLength + 33 * 2 + 1);
      macInput.set(new Uint8Array(theirIdentityPubKey));
      macInput.set(new Uint8Array(ourIdentityPubKey), 33);
      macInput[33 * 2] = (3 << 4) | 3;
      macInput.set(new Uint8Array(encodedMsg), 33 * 2 + 1);
      var keys = await Internal.HKDF(util.toArrayBuffer(messageKey), new ArrayBuffer(32), "WhisperMessageKeys");
      await Internal.verifyMAC(macInput, keys[1], tag8, 8);
      var plaintext = await Internal.crypto.decrypt(keys[0], ciphertext, keys[2].slice(0, 16));
      return plaintext;
    }


    async function SignalCoreAESEnc(key, iv, data) {
      var expected = await crypto.subtle.importKey('raw', key, {
                    name: 'AES-CBC'
                }, false, ['encrypt']).then(function(key) {
                    return crypto.subtle.encrypt({
                        name: 'AES-CBC',
                        iv: new Uint8Array(iv)
                    }, key, data);
                });
      return expected;
    }

    async function SignalCoreAESDec(key, iv, data) {
      return crypto.subtle.importKey('raw', key, {
          name: 'AES-CBC'
      }, false, ['decrypt']).then(function(key) {
          return crypto.subtle.decrypt({
              name: 'AES-CBC',
              iv: new Uint8Array(iv)
          }, key, data);
      });
    }

    async function SignalCoreHMAC(key, data) {
      var expected = await crypto.subtle.importKey('raw', key, {name: 'HMAC', hash: {name: 'SHA-256'}}, false, ['sign']).then(function(key) {
                    return crypto.subtle.sign( {name: 'HMAC', hash: 'SHA-256'}, key, data);
                });
      return expected;
    }

    function SignalCoreSHA512(data) {
      return crypto.subtle.digest({name: 'SHA-512'}, data);
    }

    function SignalCoreHKDF(input, salt, info) {
      return Internal.crypto.sign(salt, input).then(function(PRK) {
          var infoBuffer = new ArrayBuffer(info.byteLength + 1 + 32);
          var infoArray = new Uint8Array(infoBuffer);
          infoArray.set(new Uint8Array(info), 32);
          infoArray[infoArray.length - 1] = 1;
          return Internal.crypto.sign(PRK, infoBuffer.slice(32)).then(function(T1) {
              infoArray.set(new Uint8Array(T1));
              infoArray[infoArray.length - 1] = 2;
              return Internal.crypto.sign(PRK, infoBuffer).then(function(T2) {
                  infoArray.set(new Uint8Array(T2));
                  infoArray[infoArray.length - 1] = 3;
                  return Internal.crypto.sign(PRK, infoBuffer).then(function(T3) {
                      return [ T1, T2, T3 ];
                  });
              });
          });
      });
    }

    async function SignalCoreEd25519Sign(privKey, message) {
      return await Internal.Curve.async.Ed25519Sign(privKey, message);
    }

    async function SignalCoreECDHE(pubKey, privKey) {
      return Internal.Curve.async.ECDHE(pubKey, privKey);
    }
    async function SignalCoreEd25519Verify(pubKey, msg, sig) {
      return await Internal.Curve.async.Ed25519Verify(pubKey, msg, sig);
    }

    Internal.FStar = {
      checkIfInitialized:checkIfInitialized,
      SignalCoreVerifySig:SignalCoreVerifySig,
      SignalCoreSign:SignalCoreSign,
      SignalCoreGenerateRegistrationId:SignalCoreGenerateRegistrationId,
      SignalCoreCreateKeyPair:SignalCoreCreateKeyPair,
      SignalCoreRatchet:SignalCoreRatchet,
      SignalCoreInitiate:SignalCoreInitiate,
      SignalCoreRespond:SignalCoreRespond,
      SignalCoreFillMessagesKeys:SignalCoreFillMessagesKeys,
      SignalCoreEncrypt:SignalCoreEncrypt,
      SignalCoreDecrypt:SignalCoreDecrypt,
      SignalCoreAESEnc:SignalCoreAESEnc,
      SignalCoreAESDec:SignalCoreAESDec,
      SignalCoreHMAC:SignalCoreHMAC,
      SignalCoreSHA512:SignalCoreSHA512,
      SignalCoreHKDF:SignalCoreHKDF,
      SignalCoreEd25519Sign:SignalCoreEd25519Sign,
      SignalCoreECDHE:SignalCoreECDHE,
      SignalCoreEd25519Verify:SignalCoreEd25519Verify,
    }
})();
