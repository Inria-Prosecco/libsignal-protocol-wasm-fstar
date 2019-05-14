/*
 * vim: ts=4:sw=4
 */

var counter = 0;

var Internal = Internal || {};


(function() {
    'use strict';

    var crypto = window.crypto;

    if (!crypto || !crypto.subtle || typeof crypto.getRandomValues !== 'function') {
        throw new Error('WebCrypto not found');
    }

    Internal.crypto = {
        getRandomBytes: function(size) {
            var array = new Uint8Array(size);
            crypto.getRandomValues(array);
            return array.buffer;
        },
        encrypt: async function(key, data, iv) {
            return await Internal.FStar.SignalCoreAESEnc(key, iv, data);
        },
        decrypt: async function(key, data, iv) {
            return await Internal.FStar.SignalCoreAESDec(key, iv, data);
        },
        sign: async function(key, data) {
            return await Internal.FStar.SignalCoreHMAC(key, data);
        },
        hash: async function(data) {
            // return crypto.subtle.digest({name: 'SHA-512'}, data);
            return await Internal.FStar.SignalCoreSHA512(data);
        },

        // infoBuffer and infoArray are local, but the function returns newly
        // allocated arrays T1, T2 and T3.
        HKDF: async function(input, salt, info) {
            // Specific implementation of RFC 5869 that only returns the first 3 32-byte chunks
            // TODO: We dont always need the third chunk, we might skip it
            return await Internal.FStar.SignalCoreHKDF(input, salt, info);
        },

        // Curve 25519 crypto
        createKeyPair: async function(privKey) {
            return await Internal.FStar.SignalCoreCreateKeyPair(privKey);
        },
        ECDHE: async function(pubKey, privKey) {
            return await Internal.FStar.SignalCoreECDHE(pubKey, privKey);
        },
        Ed25519Sign: async function(privKey, message) {
            return await Internal.FStar.SignalCoreEd25519Sign(privKey, message);
        },
        Ed25519Verify: async function(pubKey, msg, sig) {
            let is_ok = await Internal.FStar.SignalCoreEd25519Verify(pubKey, msg, sig);
            if (!is_ok) {
              throw new Error("Invalid signature");
            }
        }
    };


    // HKDF for TextSecure has a bit of additional handling - salts always end up being 32 bytes
    Internal.HKDF = function(input, salt, info) {
        if (salt.byteLength != 32) {
            throw new Error("Got salt of incorrect length");
        }

        return Internal.crypto.HKDF(input, salt, util.toArrayBuffer(info));
    };

    Internal.verifyMAC = function(data, key, mac, length) {
        return Internal.crypto.sign(key, data).then(function(calculated_mac) {
            if (mac.byteLength != length || calculated_mac.byteLength < length) {
                throw new Error("Bad MAC length");
            }
            var a = new Uint8Array(calculated_mac);
            var b = new Uint8Array(mac);
            var result = 0;
            for (var i = 0; i < mac.byteLength; ++i) {
                result = result | (a[i] ^ b[i]);
            }
            if (result !== 0) {
                throw new Error("Bad MAC");
            }
        });
    };

    libsignal.HKDF = {
        deriveSecrets: function(input, salt, info) {
            return Internal.HKDF(input, salt, info);
        }
    };

    libsignal.crypto = {
        encrypt: function(key, data, iv) {
            return Internal.crypto.encrypt(key, data, iv);
        },
        decrypt: function(key, data, iv) {
            return Internal.crypto.decrypt(key, data, iv);
        },
        calculateMAC: function(key, data) {
            return Internal.crypto.sign(key, data);
        },
        verifyMAC: function(data, key, mac, length) {
            return Internal.verifyMAC(data, key, mac, length);
        },
        getRandomBytes: function(size) {
            return Internal.crypto.getRandomBytes(size);
        }
    };

})();
