import { deepStrictEqual } from 'node:assert';
import { should, describe } from 'micro-should';
import { bytesToHex as hex } from '@noble/hashes/utils';
import { rangeproofSign } from '../src/secp256k1';

import { default as v } from './vectors/secp256k1/rangeproof.json' with { type: 'json' };

describe('secp256k1 rangeproof', () => {
  should('sign', async () => {
      const {
          value,
          minval,
          exp,
          bits,
          genp,
          blind,
          nonce,
          script,
          msg,
          commit
        } = v.sign;

      const result = rangeproofSign(
        BigInt(minval),
        commit,
        blind,
        nonce,
        exp,
        bits,
        BigInt(value),
        msg,
        script,
        genp
      );

      deepStrictEqual(hex(result), v.sign.expected)
  });

  should('verify', async () => {
      const {
          value,
          minval,
          exp,
          bits,
          genp,
          blind,
          nonce,
          script,
          msg,
          commit
        } = v.sign;

    "scriptPubkey"
    "assetGenerator"
    "blindingPrivkey"
    "ephemeralPubkey"
    "valueCommitment"
      const result = rangeproofVerify(
    "scriptPubkey"
    "assetGenerator"
    "blindingPrivkey"
    "ephemeralPubkey"
    "valueCommitment"
      );

      deepStrictEqual(hex(result), v.sign.expected)
  });
});

should.run();
