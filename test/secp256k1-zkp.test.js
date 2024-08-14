import { deepStrictEqual } from 'node:assert';
import { should, describe } from 'micro-should';
import { bytesToHex as hex } from '@noble/hashes/utils';
import { rangeproofSign } from '../src/secp256k1.ts';

import { default as v } from './vectors/secp256k1/rangeproof.json' with { type: 'json' };

describe('secp256k1 rangeproof', () => {
  should('sign', async () => {
    let { value, minval, exp, bits, genp, blind, nonce, script, msg, commit } = v.sign;
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

    deepStrictEqual(hex(result), v.sign.expected);
  });

  should('verify', async () => {
    const { value, minval, exp, bits, genp, blind, nonce, script, msg, commit } = v.verify;

    const result = rangeproofVerify(
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

    deepStrictEqual(hex(result), v.verify.expected);
  });
});

// ESM is broken.
import url from 'node:url';
if (import.meta.url === url.pathToFileURL(process.argv[1]).href) {
  should.run();
}
