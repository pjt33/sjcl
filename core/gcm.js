/** @fileOverview GCM mode implementation.
 *
 * @author Juho Vähä-Herttua
 * @author Peter Taylor
 */

/** @namespace Galois/Counter mode. */
sjcl.mode.gcm = {
  /** The name of the mode.
   * @constant
   */
  name: "gcm",
  
  /** Encrypt in GCM mode.
   * @static
   * @param {Object} prf The pseudorandom function.  It must have a block size of 16 bytes.
   * @param {bitArray} plaintext The plaintext data.
   * @param {bitArray} iv The initialization value.
   * @param {bitArray} [adata=[]] The authenticated data.
   * @param {Number} [tlen=128] The desired tag length, in bits.
   * @return {bitArray} The encrypted data, an array of bytes.
   */
  encrypt: function (prf, plaintext, iv, adata, tlen) {
    var out, data = plaintext.slice(0), w=sjcl.bitArray;
    tlen = tlen || 128;
    adata = adata || [];

    // encrypt and tag
    out = sjcl.mode.gcm._ctrMode(true, prf, data, adata, iv, tlen);

    return w.concat(out.data, out.tag);
  },
  
  /** Decrypt in GCM mode.
   * @static
   * @param {Object} prf The pseudorandom function.  It must have a block size of 16 bytes.
   * @param {bitArray} ciphertext The ciphertext data.
   * @param {bitArray} iv The initialization value.
   * @param {bitArray} [adata=[]] The authenticated data.
   * @param {Number} [tlen=128] The desired tag length, in bits.
   * @return {bitArray} The decrypted data.
   */
  decrypt: function (prf, ciphertext, iv, adata, tlen) {
    var out, data = ciphertext.slice(0), tag, w=sjcl.bitArray, l=w.bitLength(data);
    tlen = tlen || 128;
    adata = adata || [];

    // Slice tag out of data
    if (tlen <= l) {
      tag = w.bitSlice(data, l-tlen);
      data = w.bitSlice(data, 0, l-tlen);
    } else {
      tag = data;
      data = [];
    }

    // decrypt and tag
    out = sjcl.mode.gcm._ctrMode(false, prf, data, adata, iv, tlen);

    if (!w.equal(out.tag, tag)) {
      throw new sjcl.exception.corrupt("gcm: tag doesn't match");
    }
    return out.data;
  },

  /** Precompute a table for optimised Galois multiplication; this is the "simple 8-bit tables"
   * approach described in http://csrc.nist.gov/groups/ST/toolkit/BCM/documents/proposedmodes/gcm/gcm-spec.pdf
   * @private
   */
  _precomputeGaloisTable: function(y) {
    var premul=[], i, j, k, prev, zero=[0,0,0,0], xor=sjcl.bitArray._xor4;
    for (i=0; i<16; i++) {
      premul[i]=[];
      for (j=0; j<256; j++) {
        premul[i][j] = zero;
      }
    }

    // The powers of two are simple shifts modulo the field polynomial
    prev = premul[0][0x80] = y.slice(0);
    for (i=1; i<128; i++) {
      prev = premul[i>>>3][0x80>>>(i&7)] = [
        (prev[0]>>>1) ^  (prev[3]&1)*0xe1000000,
        (prev[1]>>>1) | ((prev[0]&1)<<31),
        (prev[2]>>>1) | ((prev[1]&1)<<31),
        (prev[3]>>>1) | ((prev[2]&1)<<31)
      ];
    }

    // Fill in the non-powers of 2 by linearity
    for (i=0; i<16; i++) {
      for (j=2; j<256; j<<=1) {
        for (k=1; k<j; k++) {
          premul[i][j+k] = xor(premul[i][j], premul[i][k]);
        }
      }
    }
    return premul;
  },

  _ghash: function(premul, Y0, data) {
    var Yi=Y0.slice(0), i, j, Zi, l=data.length, xor=sjcl.bitArray._xor4;
    for (i=0; i<l; i+=4) {
      Yi[0] ^= 0xffffffff&data[i];
      Yi[1] ^= 0xffffffff&data[i+1];
      Yi[2] ^= 0xffffffff&data[i+2];
      Yi[3] ^= 0xffffffff&data[i+3];

      Zi = [0,0,0,0];
      for (j=0; j<16; j++) {
        Zi = xor(Zi, premul[j][Yi[j>>>2]>>>(8*(3-j&3)) & 255]);
      }
      Yi = Zi;
    }
    return Yi;
  },

  /** GCM CTR mode.
   * Encrypt or decrypt data and tag with the prf in GCM-style CTR mode.
   * @param {Boolean} encrypt True if encrypt, false if decrypt.
   * @param {Object} prf The PRF.
   * @param {bitArray} data The data to be encrypted or decrypted.
   * @param {bitArray} iv The initialization vector.
   * @param {bitArray} adata The associated data to be tagged.
   * @param {Number} tlen The length of the tag, in bits.
   */
  _ctrMode: function(encrypt, prf, data, adata, iv, tlen) {
    var H, premul, J0, S0, enc, i, ctr, tag, last, l, bl, abl, ivbl, w=sjcl.bitArray, ghash=sjcl.mode.gcm._ghash;

    // Calculate data lengths
    l = data.length;
    bl = w.bitLength(data);
    abl = w.bitLength(adata);
    ivbl = w.bitLength(iv);

    // Calculate the parameters
    H = prf.encrypt([0,0,0,0]);
    premul = sjcl.mode.gcm._precomputeGaloisTable(H);
    if (ivbl === 96) {
      J0 = iv.slice(0);
      J0 = w.concat(J0, [1]);
    } else {
      J0 = ghash(premul, [0,0,0,0], iv);
      J0 = ghash(premul, J0, [0,0,Math.floor(ivbl/0x100000000),ivbl&0xffffffff]);
    }
    S0 = ghash(premul, [0,0,0,0], adata);

    // Initialize ctr and tag
    ctr = J0.slice(0);
    tag = S0.slice(0);

    // If decrypting, calculate hash
    if (!encrypt) {
      tag = ghash(premul, S0, data);
    }

    // Encrypt all the data
    for (i=0; i<l; i+=4) {
       ctr[3]++;
       enc = prf.encrypt(ctr);
       data[i]   ^= enc[0];
       data[i+1] ^= enc[1];
       data[i+2] ^= enc[2];
       data[i+3] ^= enc[3];
    }
    data = w.clamp(data, bl);

    // If encrypting, calculate hash
    if (encrypt) {
      tag = ghash(premul, S0, data);
    }

    // Calculate last block from bit lengths, ugly because bitwise operations are 32-bit
    last = [
      Math.floor(abl/0x100000000), abl&0xffffffff,
      Math.floor(bl/0x100000000), bl&0xffffffff
    ];

    // Calculate the final tag block
    tag = ghash(premul, tag, last);
    enc = prf.encrypt(J0);
    tag[0] ^= enc[0];
    tag[1] ^= enc[1];
    tag[2] ^= enc[2];
    tag[3] ^= enc[3];

    return { tag:w.bitSlice(tag, 0, tlen), data:data };
  }
};
