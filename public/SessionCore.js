(function() {
    'use strict';
    var chainStore = []
    var sessionStore = []

    async function CoreInitSessionInitiator(
      session,
      deviceSignedPreKeyPub,
      deviceIdentityKey,
      ourIdentityKeyPair,
      devicePreKey) {

      session.indexInfo.remoteIdentityKey = deviceIdentityKey;
      var baseKey = await Internal.crypto.createKeyPair();
      session.indexInfo.baseKey = baseKey.pubKey;
      var ourSendingEphemeralKey = await Internal.crypto.createKeyPair();
      chainStore[session.id] = [];
      chainStore[session.id][util.toString(ourSendingEphemeralKey.pubKey)] = {
        chainKey: {
          counter: -1,
          key: {}
        },
        messageKeys: [],
        chainType: Internal.ChainType.SENDING,
      };
      sessionStore[session.id] = {
        currentRatchet: {
          lastRemoteEphemeralKey: deviceSignedPreKeyPub,
          rootKey: {},
          ephemeralKeyPair: {
              privKey: {},
              pubKey: {}
          },
          previousCounter: session.currentRatchet.previousCounter
        },
        indexInfo: {
          remoteIdentityKey: deviceIdentityKey,
        },
        id: session.id
      }
      var devicePreKeyArg;
      if (devicePreKey !== undefined) {
        devicePreKeyArg = devicePreKey;
      } else {
        devicePreKeyArg = new ArrayBuffer(33);
      }
      session.currentRatchet.ephemeralKeyPair = ourSendingEphemeralKey
      var newKeys = await Internal.FStar.SignalCoreInitiate(
        ourIdentityKeyPair.privKey,
        baseKey.privKey,
        ourSendingEphemeralKey.privKey,
        sessionStore[session.id].indexInfo.remoteIdentityKey,
        sessionStore[session.id].currentRatchet.lastRemoteEphemeralKey,
        devicePreKeyArg,
        devicePreKey !== undefined
      );
      var newRootKey = newKeys[0];
      var newChainKey = newKeys[1];
      sessionStore[session.id].currentRatchet.rootKey = newRootKey;
      chainStore[session.id][util.toString(ourSendingEphemeralKey.pubKey)].chainKey.key = newChainKey
      sessionStore[session.id].currentRatchet.ephemeralKeyPair = ourSendingEphemeralKey;
      session.pendingPreKey.baseKey = baseKey.pubKey;
    }

    async function CoreInitSessionResponder(
      registrationId,
      theirEphemeralPubKey,
      ourSignedKey,
      theirIdentityPubKey,
      ourEphemeralKey,
      ourIdentityKey
    ) {
      var session = {
        registrationId: registrationId,
        currentRatchet: {
          previousCounter: 0,
          rootKey: {},
          ephemeralKeyPair: {
              privKey: {},
              pubKey: {}
          },
          lastRemoteEphemeralKey: {}
        },
        indexInfo: {
          remoteIdentityKey: theirIdentityPubKey,
          closed: -1,
          baseKey: theirEphemeralPubKey,
          baseKeyType: Internal.BaseKeyType.THEIRS,
        },
        oldRatchetList: [],
        id: freshSessionId()
      };
      sessionStore[session.id] = {
        currentRatchet: {
          lastRemoteEphemeralKey: theirEphemeralPubKey,
          ephemeralKeyPair: ourSignedKey,
          previousCounter: session.currentRatchet.previousCounter,
          rootKey: {}
        },
        indexInfo: {
          remoteIdentityKey: theirIdentityPubKey,
        },
        id: session.id
      };
      var ourEphemeralKeyArg;
      if (ourEphemeralKey !== undefined) {
        ourEphemeralKeyArg = ourEphemeralKey.privKey;
      } else {
        ourEphemeralKeyArg = new ArrayBuffer(32);
      }
      var newRootKey = await Internal.FStar.SignalCoreRespond(
          ourIdentityKey.privKey,
          ourSignedKey.privKey,
          ourEphemeralKeyArg,
          ourEphemeralKey !== undefined,
          theirIdentityPubKey,
          theirEphemeralPubKey
      );
      sessionStore[session.id].currentRatchet.rootKey = newRootKey;

      return session;
    }

    async function CoreFillMessageKeys(chain, counter) {
      if (chain.chainKey.counter >= counter) {
        return; // Already calculated
      }

      if (counter - chain.chainKey.counter > 2000) {
        throw new Error('Over 2000 messages into the future!');
      }
      if (chain.chainKey.key === undefined) {
        throw new Error("Got invalid request to extend chain after it was already closed");
      }

      var key = util.toArrayBuffer(chain.chainKey.key);
      var newKeys = await Internal.FStar.SignalCoreFillMessagesKeys(
        key
      );
      var newMac = newKeys[0];
      var newChainKey = newKeys[1];
      chain.messageKeys[chain.chainKey.counter + 1] = newMac;
      chain.chainKey.key = newChainKey;
      chain.chainKey.counter += 1;
      return CoreFillMessageKeys(chain, counter);
    }

    async function CoreEncrypt(buffer, session, ourIdentityKey) {
      var chain = chainStore[session.id][util.toString(util.toArrayBuffer(
        sessionStore[session.id].currentRatchet.ephemeralKeyPair.pubKey
      ))];
      chain.id = util.toString(util.toArrayBuffer(
        sessionStore[session.id].currentRatchet.ephemeralKeyPair.pubKey
      ));
      await CoreFillMessageKeys(chain, chain.chainKey.counter + 1);
      if (chain.chainType === Internal.ChainType.RECEIVING) {
        throw new Error("Tried to encrypt on a receiving chain");
      }
      var result = await Internal.FStar.SignalCoreEncrypt(
        util.toArrayBuffer(ourIdentityKey.pubKey),
        util.toArrayBuffer(sessionStore[session.id].indexInfo.remoteIdentityKey),
        chain.messageKeys[chain.chainKey.counter],
        util.toArrayBuffer(
         sessionStore[session.id].currentRatchet.ephemeralKeyPair.pubKey
        ),
        sessionStore[session.id].currentRatchet.previousCounter,
        chain.chainKey.counter,
        buffer,
      );
      delete chain.messageKeys[chain.chainKey.counter];
      return result;
    }


    // Never called outside the module
    async function CoreCalculateRatchet(session, remoteKey, sending) {
      var ratchet = session.currentRatchet;
      var ephemeralPublicKey;
      if (sending) {
        ephemeralPublicKey = ratchet.ephemeralKeyPair.pubKey;
      } else {
        ephemeralPublicKey = remoteKey;
      }
      chainStore[session.id][util.toString(ephemeralPublicKey)] = {
        chainKey: {
          counter: -1,
          key: {}
        },
        messageKeys: [],
        chainType: sending ? Internal.ChainType.SENDING : Internal.ChainType.RECEIVING,
      }
      var newKeys = await Internal.FStar.SignalCoreRatchet(
        util.toArrayBuffer(sessionStore[session.id].currentRatchet.rootKey),
        util.toArrayBuffer(sessionStore[session.id].currentRatchet.ephemeralKeyPair.privKey),
        remoteKey
      )
      var newRootKey = newKeys[0];
      var newChainKey = newKeys[1];
      chainStore[session.id][util.toString(ephemeralPublicKey)].chainKey.key = newChainKey;
      sessionStore[session.id].currentRatchet.rootKey = newRootKey;
    }

    async function CoreDecrypt(messageProto, decodeMessage, mac, session, ourIdentityKey) {
      var message = decodeMessage(messageProto);
      var remoteEphemeralKey = message.ephemeralKey.toArrayBuffer();
      if (chainStore[session.id] === undefined) {
        chainStore[session.id] = {}
      }
      if (chainStore[session.id][util.toString(remoteEphemeralKey)] === undefined) {
        console.log('New remote ephemeral key');
        var ratchet = sessionStore[session.id].currentRatchet;

        var previousRatchet = chainStore[session.id][util.toString(ratchet.lastRemoteEphemeralKey)];
        if (previousRatchet !== undefined) {
          await CoreFillMessageKeys(previousRatchet, message.previousCounter);
          delete previousRatchet.chainKey.key;
        }
        await CoreCalculateRatchet(sessionStore[session.id], remoteEphemeralKey, false);
        // Now swap the ephemeral key and calculate the new sending chain
        var previousRatchet = util.toString(ratchet.ephemeralKeyPair.pubKey);
        if (chainStore[session.id][previousRatchet] !== undefined) {
          ratchet.previousCounter = chainStore[session.id][previousRatchet].chainKey.counter;
          delete chainStore[session.id][previousRatchet];
        }

        var keyPair = await Internal.crypto.createKeyPair();
        ratchet.ephemeralKeyPair = keyPair;
        await CoreCalculateRatchet(
          sessionStore[session.id],
          remoteEphemeralKey,
          true
        );
        ratchet.lastRemoteEphemeralKey = remoteEphemeralKey;
      }
      var chain = chainStore[session.id][util.toString(message.ephemeralKey)];
      await CoreFillMessageKeys(chain, message.counter);
      if (chain.chainType === Internal.ChainType.SENDING) {
        throw new Error("Tried to decrypt on a sending chain");
      }
      var messageKey = chain.messageKeys[message.counter];
      if (messageKey === undefined) {
        var e = new Error("Message key not found. The counter was repeated or the key was not filled.");
        e.name = 'MessageCounterError';
        throw e;
      }
      delete chain.messageKeys[message.counter];
      var plaintext = await Internal.FStar.SignalCoreDecrypt(
        util.toArrayBuffer(ourIdentityKey.pubKey),
        util.toArrayBuffer(sessionStore[session.id].indexInfo.remoteIdentityKey),
        remoteEphemeralKey,
        messageKey,
        message.previousCounter,
        message.counter,
        message.ciphertext.toArrayBuffer(),
        mac,
      );
      delete session.pendingPreKey;
      return plaintext;
    }

    Internal.Core = {
      CoreInitSessionInitiator: CoreInitSessionInitiator,
      CoreInitSessionResponder: CoreInitSessionResponder,
      CoreEncrypt: CoreEncrypt,
      CoreDecrypt: CoreDecrypt,
    }
})();
