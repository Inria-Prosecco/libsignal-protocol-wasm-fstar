function SessionBuilder(storage, remoteAddress) {
  this.remoteAddress = remoteAddress;
  this.storage = storage;
}

var sessionId = 0;

function freshSessionId() {
  var res = sessionId;
  sessionId += 1;
  return res;
}

SessionBuilder.prototype = {
  processPreKey: function(device) {
    return Internal.SessionLock.queueJobForNumber(this.remoteAddress.toString(), async function() {
      var trusted = await this.storage.isTrustedIdentity(
        this.remoteAddress.getName(), device.identityKey, this.storage.Direction.SENDING
      )
      if (!trusted) {
        throw new Error('Identity key changed');
      }
      var ourIdentityKey = await this.storage.getIdentityKeyPair();
      var address = this.remoteAddress.toString();
      var serialized = await this.storage.loadSession(address);
      var record;
      if (serialized !== undefined) {
        record = Internal.SessionRecord.deserialize(serialized);
      } else {
        record = new Internal.SessionRecord();
      }
      var session = {
        registrationId: device.registrationId,
        currentRatchet: {
          previousCounter: 0,
        },
        indexInfo: {
          closed: -1,
          baseKeyType: Internal.BaseKeyType.OURS
        },
        oldRatchetList: [],
        pendingPreKey: {
          signedKeyId: device.signedPreKey.keyId,
        },
        id: freshSessionId()
      };
      var devicePreKey;
      if (device.preKey) {
        devicePreKey = device.preKey.publicKey;
      }
      await Internal.FStar.SignalCoreVerifySig(
        device.identityKey,
        device.signedPreKey.publicKey,
        device.signedPreKey.signature
      );

      await Internal.Core.CoreInitSessionInitiator(
        session,
        device.signedPreKey.publicKey,
        device.identityKey,
        ourIdentityKey,
        devicePreKey
      );
      if (device.preKey) {
        session.pendingPreKey.preKeyId = device.preKey.keyId;
      }
      record.archiveCurrentState();
      record.updateSessionState(session);
      await this.storage.storeSession(address, record.serialize());
      await this.storage.saveIdentity(this.remoteAddress.toString(), session.indexInfo.remoteIdentityKey);
    }.bind(this))
  },
  processV3: function(record, message) {
    var preKeyPair, signedPreKeyPair, session;
    return this.storage.isTrustedIdentity(
      this.remoteAddress.getName(), message.identityKey.toArrayBuffer(), this.storage.Direction.RECEIVING
    ).then(function(trusted) {
      if (!trusted) {
        var e = new Error('Unknown identity key');
        e.identityKey = message.identityKey.toArrayBuffer();
        throw e;
      }
      return Promise.all([
        this.storage.loadPreKey(message.preKeyId),
        this.storage.loadSignedPreKey(message.signedPreKeyId),
      ]).then(function(results) {
        preKeyPair = results[0];
        signedPreKeyPair = results[1];
      });
    }.bind(this)).then(function() {
      session = record.getSessionByBaseKey(message.baseKey);
      if (session) {
        console.log("Duplicate PreKeyMessage for session");
        return;
      }

      session = record.getOpenSession();

      if (signedPreKeyPair === undefined) {
        // Session may or may not be the right one, but if its not, we
        // can't do anything about it ...fall through and let
        // decryptWhisperMessage handle that case
        if (session !== undefined && session.currentRatchet !== undefined) {
          return;
        } else {
          throw new Error("Missing Signed PreKey for PreKeyWhisperMessage");
        }
      }

      if (session !== undefined) {
        record.archiveCurrentState();
      }
      if (message.preKeyId && !preKeyPair) {
        console.log('Invalid prekey id', message.preKeyId);
      }
      return this.initSession(preKeyPair, signedPreKeyPair,
        message.identityKey.toArrayBuffer(),
        message.baseKey.toArrayBuffer(), message.registrationId
      ).then(function(new_session) {
        // Note that the session is not actually saved until the very
        // end of decryptWhisperMessage ... to ensure that the sender
        // actually holds the private keys for all reported pubkeys
        record.updateSessionState(new_session);
        return this.storage.saveIdentity(this.remoteAddress.toString(), message.identityKey.toArrayBuffer()).then(function() {
          return message.preKeyId;
        });
      }.bind(this));
    }.bind(this));
  },
  initSession: async function(ourEphemeralKey, ourSignedKey,
    theirIdentityPubKey, theirEphemeralPubKey,
    registrationId) {
    var ourIdentityKey = await this.storage.getIdentityKeyPair();
    return await Internal.Core.CoreInitSessionResponder(
      registrationId,
      theirEphemeralPubKey,
      ourSignedKey,
      theirIdentityPubKey,
      ourEphemeralKey,
      ourIdentityKey
    );
  },
};

libsignal.SessionBuilder = function(storage, remoteAddress) {
  var builder = new SessionBuilder(storage, remoteAddress);
  this.processPreKey = builder.processPreKey.bind(builder);
  this.processV3 = builder.processV3.bind(builder);
};
