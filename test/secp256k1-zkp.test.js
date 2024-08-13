import { deepStrictEqual } from 'node:assert';
import { should, describe } from 'micro-should';
import { bytesToHex as hex } from '@noble/hashes/utils';
import { rangeproofSign } from '../esm/secp256k1.js';

import { default as rangeproofs } from './vectors/secp256k1/rangeproof.json' with { type: 'json' };

describe('secp256k1 rangeproof sign', () => {
  should('match the test vector from liquidjs-lib', async () => {
    for (const vector of rangeproofs.valid) {
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
        } = vector;

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

      deepStrictEqual(hex(result), vector.expected)
    }
  });
});

// ESM is broken.
import url from 'node:url';
if (import.meta.url === url.pathToFileURL(process.argv[1]).href) {
  should.run();
}
