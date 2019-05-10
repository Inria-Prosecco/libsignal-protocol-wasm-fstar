function SessionCipher(storage, remoteAddress) {
  this.remoteAddress = remoteAddress;
  this.storage = storage;
}

SessionCipher.prototype = {
  getRecord: function(encodedNumber) {
    return this.storage.loadSession(encodedNumber).then(function(serialized) {
      if (serialized === undefined) {
        return undefined;
      }
      return Internal.SessionRecord.deserialize(serialized);
    });
  },
  encrypt: function(buffer, encoding) {
    buffer = dcodeIO.ByteBuffer.wrap(buffer, encoding).toArrayBuffer();
    return Internal.SessionLock.queueJobForNumber(this.remoteAddress.toString(), async function() {
      var address = this.remoteAddress.toString();
      var ourIdentityKey = await this.storage.getIdentityKeyPair();
      var myRegistrationId = await this.storage.getLocalRegistrationId();
      var record = await this.getRecord(address);
      if (!(buffer instanceof ArrayBuffer)) {
        throw new Error("Expected buffer to be an ArrayBuffer");
      }

      var ourIdentityKey, myRegistrationId, record, session;

      var address = this.remoteAddress.toString();
      if (!record) {
        throw new Error("No record for " + address);
      }
      session = record.getOpenSession();
      if (!session) {
        throw new Error("No session to encrypt message for " + address);
      }

      var result = await Internal.Core.CoreEncrypt(
        buffer,
        session,
        ourIdentityKey
      );

      var trusted = await this.storage.isTrustedIdentity(
        this.remoteAddress.getName(), util.toArrayBuffer(session.indexInfo.remoteIdentityKey), this.storage.Direction.SENDING
      )
      if (!trusted) {
        throw new Error('Identity key changed');
      }

      var message = result;
      await this.storage.saveIdentity(this.remoteAddress.toString(), session.indexInfo.remoteIdentityKey)
      record.updateSessionState(session);
      await this.storage.storeSession(address, record.serialize());

      if (session.pendingPreKey !== undefined) {
        var preKeyMsg = new Internal.protobuf.PreKeyWhisperMessage();
        preKeyMsg.identityKey = util.toArrayBuffer(ourIdentityKey.pubKey);
        preKeyMsg.registrationId = myRegistrationId;

        preKeyMsg.baseKey = util.toArrayBuffer(session.pendingPreKey.baseKey);
        if (session.pendingPreKey.preKeyId) {
          preKeyMsg.preKeyId = session.pendingPreKey.preKeyId;
        }
        preKeyMsg.signedPreKeyId = session.pendingPreKey.signedKeyId;

        preKeyMsg.message = message;
        var result = String.fromCharCode((3 << 4) | 3) + util.toString(preKeyMsg.encode());
        return {
          type: 3,
          body: result,
          registrationId: session.registrationId
        };

      } else {
        return {
          type: 1,
          body: util.toString(message),
          registrationId: session.registrationId
        };
      }
    }.bind(this));
  },
  decryptWithSessionList: function(buffer, sessionList, errors) {
    // Iterate recursively through the list, attempting to decrypt
    // using each one at a time. Stop and return the result if we get
    // a valid result
    if (sessionList.length === 0) {
      return Promise.reject(errors[0]);
    }

    var session = sessionList.pop();
    return this.doDecryptWhisperMessage(buffer, session).then(function(plaintext) {
      return {
        plaintext: plaintext,
        session: session
      };
    }).catch(function(e) {
      if (e.name === 'MessageCounterError') {
        return Promise.reject(e);
      }

      errors.push(e);
      return this.decryptWithSessionList(buffer, sessionList, errors);
    }.bind(this));
  },
  decryptWhisperMessage: function(buffer, encoding) {
    buffer = dcodeIO.ByteBuffer.wrap(buffer, encoding).toArrayBuffer();
    return Internal.SessionLock.queueJobForNumber(this.remoteAddress.toString(), function() {
      var address = this.remoteAddress.toString();
      return this.getRecord(address).then(function(record) {
        if (!record) {
          throw new Error("No record for device " + address);
        }
        var errors = [];
        return this.decryptWithSessionList(buffer, record.getSessions(), errors).then(function(result) {
          return this.getRecord(address).then(function(record) {
            if (result.session.indexInfo.baseKey !== record.getOpenSession().indexInfo.baseKey) {
              record.archiveCurrentState();
              record.promoteState(result.session);
            }

            return this.storage.isTrustedIdentity(
              this.remoteAddress.getName(), util.toArrayBuffer(result.session.indexInfo.remoteIdentityKey), this.storage.Direction.RECEIVING
            ).then(function(trusted) {
              if (!trusted) {
                throw new Error('Identity key changed');
              }
            }).then(function() {
              return this.storage.saveIdentity(this.remoteAddress.toString(), result.session.indexInfo.remoteIdentityKey);
            }.bind(this)).then(function() {
              record.updateSessionState(result.session);
              return this.storage.storeSession(address, record.serialize()).then(function() {
                return result.plaintext;
              });
            }.bind(this));
          }.bind(this));
        }.bind(this));
      }.bind(this));
    }.bind(this));
  },
  decryptPreKeyWhisperMessage: function(buffer, encoding) {
    buffer = dcodeIO.ByteBuffer.wrap(buffer, encoding);
    var version = buffer.readUint8();
    if ((version & 0xF) > 3 || (version >> 4) < 3) { // min version > 3 or max version < 3
      throw new Error("Incompatible version number on PreKeyWhisperMessage");
    }
    return Internal.SessionLock.queueJobForNumber(this.remoteAddress.toString(), function() {
      var address = this.remoteAddress.toString();
      return this.getRecord(address).then(function(record) {
        var preKeyProto = Internal.protobuf.PreKeyWhisperMessage.decode(buffer);
        if (!record) {
          if (preKeyProto.registrationId === undefined) {
            throw new Error("No registrationId");
          }
          record = new Internal.SessionRecord(
            preKeyProto.registrationId
          );
        }
        var builder = new SessionBuilder(this.storage, this.remoteAddress);
        // isTrustedIdentity is called within processV3, no need to call it here
        return builder.processV3(record, preKeyProto).then(function(preKeyId) {
          var session = record.getSessionByBaseKey(preKeyProto.baseKey);
          return this.doDecryptWhisperMessage(
            preKeyProto.message.toArrayBuffer(), session
          ).then(function(plaintext) {
            record.updateSessionState(session);
            return this.storage.storeSession(address, record.serialize()).then(function() {
              if (preKeyId !== undefined && preKeyId !== null) {
                return this.storage.removePreKey(preKeyId);
              }
            }.bind(this)).then(function() {
              return plaintext;
            });
          }.bind(this));
        }.bind(this));
      }.bind(this));
    }.bind(this));
  },
  doDecryptWhisperMessage: async function(messageBytes, session) {
    if (!(messageBytes instanceof ArrayBuffer)) {
      throw new Error("Expected messageBytes to be an ArrayBuffer");
    }
    var version = (new Uint8Array(messageBytes))[0];
    if ((version & 0xF) > 3 || (version >> 4) < 3) { // min version > 3 or max version < 3
      throw new Error("Incompatible version number on WhisperMessage");
    }
    var ourIdentityKey = await this.storage.getIdentityKeyPair();
    if (session === undefined) {
      return Promise.reject(new Error("No session found to decrypt message from " + remoteAddress.toString()));
    }
    if (session.indexInfo.closed != -1) {
      console.log('decrypting message for closed session');
    }
    var messageProto = messageBytes.slice(1, messageBytes.byteLength - 8);
    var mac = messageBytes.slice(messageBytes.byteLength - 8, messageBytes.byteLength);

    var decodeMessage = Internal.protobuf.WhisperMessage.decode;
    return Internal.Core.CoreDecrypt(messageProto, decodeMessage, mac, session, ourIdentityKey);
  },
  getRemoteRegistrationId: function() {
    return Internal.SessionLock.queueJobForNumber(this.remoteAddress.toString(), function() {
      return this.getRecord(this.remoteAddress.toString()).then(function(record) {
        if (record === undefined) {
          return undefined;
        }
        var openSession = record.getOpenSession();
        if (openSession === undefined) {
          return null;
        }
        return openSession.registrationId;
      });
    }.bind(this));
  },
  hasOpenSession: function() {
    return Internal.SessionLock.queueJobForNumber(this.remoteAddress.toString(), function() {
      return this.getRecord(this.remoteAddress.toString()).then(function(record) {
        if (record === undefined) {
          return false;
        }
        return record.haveOpenSession();
      });
    }.bind(this));
  },
  closeOpenSessionForDevice: function() {
    var address = this.remoteAddress.toString();
    return Internal.SessionLock.queueJobForNumber(address, function() {
      return this.getRecord(address).then(function(record) {
        if (record === undefined || record.getOpenSession() === undefined) {
          return;
        }

        record.archiveCurrentState();
        return this.storage.storeSession(address, record.serialize());
      }.bind(this));
    }.bind(this));
  },
  deleteAllSessionsForDevice: function() {
    // Used in session reset scenarios, where we really need to delete
    var address = this.remoteAddress.toString();
    return Internal.SessionLock.queueJobForNumber(address, function() {
      return this.getRecord(address).then(function(record) {
        if (record === undefined) {
          return;
        }

        record.deleteAllSessions();
        return this.storage.storeSession(address, record.serialize());
      }.bind(this));
    }.bind(this));
  }
};

libsignal.SessionCipher = function(storage, remoteAddress) {
  var cipher = new SessionCipher(storage, remoteAddress);

  // returns a Promise that resolves to a ciphertext object
  this.encrypt = cipher.encrypt.bind(cipher);

  // returns a Promise that inits a session if necessary and resolves
  // to a decrypted plaintext array buffer
  this.decryptPreKeyWhisperMessage = cipher.decryptPreKeyWhisperMessage.bind(cipher);

  // returns a Promise that resolves to decrypted plaintext array buffer
  this.decryptWhisperMessage = cipher.decryptWhisperMessage.bind(cipher);

  this.getRemoteRegistrationId = cipher.getRemoteRegistrationId.bind(cipher);
  this.hasOpenSession = cipher.hasOpenSession.bind(cipher);
  this.closeOpenSessionForDevice = cipher.closeOpenSessionForDevice.bind(cipher);
  this.deleteAllSessionsForDevice = cipher.deleteAllSessionsForDevice.bind(cipher);
};
