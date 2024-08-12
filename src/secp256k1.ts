/*! noble-curves - MIT License (c) 2022 Paul Miller (paulmillr.com) */
import { sha256 } from '@noble/hashes/sha256';
import { hmac } from '@noble/hashes/hmac';
import { randomBytes } from '@noble/hashes/utils';
import { createCurve } from './_shortw_utils.js';
import { createHasher, isogenyMap } from './abstract/hash-to-curve.js';
import { Field, mod, pow2, FpIsSquare } from './abstract/modular.js';
import type { Hex, PrivKey } from './abstract/utils.js';
import {
  inRange,
  aInRange,
  bytesToNumberBE,
  concatBytes,
  ensureBytes,
  numberToBytesBE,
} from './abstract/utils.js';
import { ProjPointType as PointType, mapToCurveSimpleSWU } from './abstract/weierstrass.js';

const secp256k1P = BigInt('0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f');
const secp256k1N = BigInt('0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141');
const _1n = BigInt(1);
const _2n = BigInt(2);
const divNearest = (a: bigint, b: bigint) => (a + b / _2n) / b;

/**
 * √n = n^((p+1)/4) for fields p = 3 mod 4. We unwrap the loop and multiply bit-by-bit.
 * (P+1n/4n).toString(2) would produce bits [223x 1, 0, 22x 1, 4x 0, 11, 00]
 */
function sqrtMod(y: bigint): bigint {
  const P = secp256k1P;
  // prettier-ignore
  const _3n = BigInt(3), _6n = BigInt(6), _11n = BigInt(11), _22n = BigInt(22);
  // prettier-ignore
  const _23n = BigInt(23), _44n = BigInt(44), _88n = BigInt(88);
  const b2 = (y * y * y) % P; // x^3, 11
  const b3 = (b2 * b2 * y) % P; // x^7
  const b6 = (pow2(b3, _3n, P) * b3) % P;
  const b9 = (pow2(b6, _3n, P) * b3) % P;
  const b11 = (pow2(b9, _2n, P) * b2) % P;
  const b22 = (pow2(b11, _11n, P) * b11) % P;
  const b44 = (pow2(b22, _22n, P) * b22) % P;
  const b88 = (pow2(b44, _44n, P) * b44) % P;
  const b176 = (pow2(b88, _88n, P) * b88) % P;
  const b220 = (pow2(b176, _44n, P) * b44) % P;
  const b223 = (pow2(b220, _3n, P) * b3) % P;
  const t1 = (pow2(b223, _23n, P) * b22) % P;
  const t2 = (pow2(t1, _6n, P) * b2) % P;
  const root = pow2(t2, _2n, P);
  if (!Fp.eql(Fp.sqr(root), y)) throw new Error('Cannot find square root');
  return root;
}

const Fp = Field(secp256k1P, undefined, undefined, { sqrt: sqrtMod });

/**
 * secp256k1 short weierstrass curve and ECDSA signatures over it.
 */
export const secp256k1 = createCurve(
  {
    a: BigInt(0), // equation params: a, b
    b: BigInt(7), // Seem to be rigid: bitcointalk.org/index.php?topic=289795.msg3183975#msg3183975
    Fp, // Field's prime: 2n**256n - 2n**32n - 2n**9n - 2n**8n - 2n**7n - 2n**6n - 2n**4n - 1n
    n: secp256k1N, // Curve order, total count of valid points in the field
    // Base point (x, y) aka generator point
    Gx: BigInt('55066263022277343669578718895168534326250603453777594175500187360389116729240'),
    Gy: BigInt('32670510020758816978083085130507043184471273380659243275938904335757337482424'),
    h: BigInt(1), // Cofactor
    lowS: true, // Allow only low-S signatures by default in sign() and verify()
    /**
     * secp256k1 belongs to Koblitz curves: it has efficiently computable endomorphism.
     * Endomorphism uses 2x less RAM, speeds up precomputation by 2x and ECDH / key recovery by 20%.
     * For precomputed wNAF it trades off 1/2 init time & 1/3 ram for 20% perf hit.
     * Explanation: https://gist.github.com/paulmillr/eb670806793e84df628a7c434a873066
     */
    endo: {
      beta: BigInt('0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee'),
      splitScalar: (k: bigint) => {
        const n = secp256k1N;
        const a1 = BigInt('0x3086d221a7d46bcde86c90e49284eb15');
        const b1 = -_1n * BigInt('0xe4437ed6010e88286f547fa90abfe4c3');
        const a2 = BigInt('0x114ca50f7a8e2f3f657c1108d9d44cfd8');
        const b2 = a1;
        const POW_2_128 = BigInt('0x100000000000000000000000000000000'); // (2n**128n).toString(16)

        const c1 = divNearest(b2 * k, n);
        const c2 = divNearest(-b1 * k, n);
        let k1 = mod(k - c1 * a1 - c2 * a2, n);
        let k2 = mod(-c1 * b1 - c2 * b2, n);
        const k1neg = k1 > POW_2_128;
        const k2neg = k2 > POW_2_128;
        if (k1neg) k1 = n - k1;
        if (k2neg) k2 = n - k2;
        if (k1 > POW_2_128 || k2 > POW_2_128) {
          throw new Error('splitScalar: Endomorphism failed, k=' + k);
        }
        return { k1neg, k1, k2neg, k2 };
      },
    },
  },
  sha256
);

// Schnorr signatures are superior to ECDSA from above. Below is Schnorr-specific BIP0340 code.
// https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki
const _0n = BigInt(0);
/** An object mapping tags to their tagged hash prefix of [SHA256(tag) | SHA256(tag)] */
const TAGGED_HASH_PREFIXES: { [tag: string]: Uint8Array } = {};
function taggedHash(tag: string, ...messages: Uint8Array[]): Uint8Array {
  let tagP = TAGGED_HASH_PREFIXES[tag];
  if (tagP === undefined) {
    const tagH = sha256(Uint8Array.from(tag, (c) => c.charCodeAt(0)));
    tagP = concatBytes(tagH, tagH);
    TAGGED_HASH_PREFIXES[tag] = tagP;
  }
  return sha256(concatBytes(tagP, ...messages));
}

// ECDSA compact points are 33-byte. Schnorr is 32: we strip first byte 0x02 or 0x03
const pointToBytes = (point: PointType<bigint>) => point.toRawBytes(true).slice(1);
const numTo32b = (n: bigint) => numberToBytesBE(n, 32);
const modP = (x: bigint) => mod(x, secp256k1P);
const modN = (x: bigint) => mod(x, secp256k1N);
const Point = secp256k1.ProjectivePoint;
const GmulAdd = (Q: PointType<bigint>, a: bigint, b: bigint) =>
  Point.BASE.multiplyAndAddUnsafe(Q, a, b);

// Calculate point, scalar and bytes
function schnorrGetExtPubKey(priv: PrivKey) {
  let d_ = secp256k1.utils.normPrivateKeyToScalar(priv); // same method executed in fromPrivateKey
  let p = Point.fromPrivateKey(d_); // P = d'⋅G; 0 < d' < n check is done inside
  const scalar = p.hasEvenY() ? d_ : modN(-d_);
  return { scalar: scalar, bytes: pointToBytes(p) };
}
/**
 * lift_x from BIP340. Convert 32-byte x coordinate to elliptic curve point.
 * @returns valid point checked for being on-curve
 */
function lift_x(x: bigint): PointType<bigint> {
  aInRange('x', x, _1n, secp256k1P); // Fail if x ≥ p.
  const xx = modP(x * x);
  const c = modP(xx * x + BigInt(7)); // Let c = x³ + 7 mod p.
  let y = sqrtMod(c); // Let y = c^(p+1)/4 mod p.
  if (y % _2n !== _0n) y = modP(-y); // Return the unique point P such that x(P) = x and
  const p = new Point(x, y, _1n); // y(P) = y if y mod 2 = 0 or y(P) = p-y otherwise.
  p.assertValidity();
  return p;
}
const num = bytesToNumberBE;
/**
 * Create tagged hash, convert it to bigint, reduce modulo-n.
 */
function challenge(...args: Uint8Array[]): bigint {
  return modN(num(taggedHash('BIP0340/challenge', ...args)));
}

/**
 * Schnorr public key is just `x` coordinate of Point as per BIP340.
 */
function schnorrGetPublicKey(privateKey: Hex): Uint8Array {
  return schnorrGetExtPubKey(privateKey).bytes; // d'=int(sk). Fail if d'=0 or d'≥n. Ret bytes(d'⋅G)
}

/**
 * Creates Schnorr signature as per BIP340. Verifies itself before returning anything.
 * auxRand is optional and is not the sole source of k generation: bad CSPRNG won't be dangerous.
 */
function schnorrSign(
  message: Hex,
  privateKey: PrivKey,
  auxRand: Hex = randomBytes(32)
): Uint8Array {
  const m = ensureBytes('message', message);
  const { bytes: px, scalar: d } = schnorrGetExtPubKey(privateKey); // checks for isWithinCurveOrder
  const a = ensureBytes('auxRand', auxRand, 32); // Auxiliary random data a: a 32-byte array
  const t = numTo32b(d ^ num(taggedHash('BIP0340/aux', a))); // Let t be the byte-wise xor of bytes(d) and hash/aux(a)
  const rand = taggedHash('BIP0340/nonce', t, px, m); // Let rand = hash/nonce(t || bytes(P) || m)
  const k_ = modN(num(rand)); // Let k' = int(rand) mod n
  if (k_ === _0n) throw new Error('sign failed: k is zero'); // Fail if k' = 0.
  const { bytes: rx, scalar: k } = schnorrGetExtPubKey(k_); // Let R = k'⋅G.
  const e = challenge(rx, px, m); // Let e = int(hash/challenge(bytes(R) || bytes(P) || m)) mod n.
  const sig = new Uint8Array(64); // Let sig = bytes(R) || bytes((k + ed) mod n).
  sig.set(rx, 0);
  sig.set(numTo32b(modN(k + e * d)), 32);
  // If Verify(bytes(P), m, sig) (see below) returns failure, abort
  if (!schnorrVerify(sig, m, px)) throw new Error('sign: Invalid signature produced');
  return sig;
}

/**
 * Verifies Schnorr signature.
 * Will swallow errors & return false except for initial type validation of arguments.
 */
function schnorrVerify(signature: Hex, message: Hex, publicKey: Hex): boolean {
  const sig = ensureBytes('signature', signature, 64);
  const m = ensureBytes('message', message);
  const pub = ensureBytes('publicKey', publicKey, 32);
  try {
    const P = lift_x(num(pub)); // P = lift_x(int(pk)); fail if that fails
    const r = num(sig.subarray(0, 32)); // Let r = int(sig[0:32]); fail if r ≥ p.
    if (!inRange(r, _1n, secp256k1P)) return false;
    const s = num(sig.subarray(32, 64)); // Let s = int(sig[32:64]); fail if s ≥ n.
    if (!inRange(s, _1n, secp256k1N)) return false;
    const e = challenge(numTo32b(r), pointToBytes(P), m); // int(challenge(bytes(r)||bytes(P)||m))%n
    const R = GmulAdd(P, s, modN(-e)); // R = s⋅G - e⋅P
    if (!R || !R.hasEvenY() || R.toAffine().x !== r) return false; // -eP == (n-e)P
    return true; // Fail if is_infinite(R) / not has_even_y(R) / x(R) ≠ r.
  } catch (error) {
    return false;
  }
}

/**
 * Schnorr signatures over secp256k1.
 */
export const schnorr = /* @__PURE__ */ (() => ({
  getPublicKey: schnorrGetPublicKey,
  sign: schnorrSign,
  verify: schnorrVerify,
  utils: {
    randomPrivateKey: secp256k1.utils.randomPrivateKey,
    lift_x,
    pointToBytes,
    numberToBytesBE,
    bytesToNumberBE,
    taggedHash,
    mod,
  },
}))();

const isoMap = /* @__PURE__ */ (() =>
  isogenyMap(
    Fp,
    [
      // xNum
      [
        '0x8e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38daaaaa8c7',
        '0x7d3d4c80bc321d5b9f315cea7fd44c5d595d2fc0bf63b92dfff1044f17c6581',
        '0x534c328d23f234e6e2a413deca25caece4506144037c40314ecbd0b53d9dd262',
        '0x8e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38e38daaaaa88c',
      ],
      // xDen
      [
        '0xd35771193d94918a9ca34ccbb7b640dd86cd409542f8487d9fe6b745781eb49b',
        '0xedadc6f64383dc1df7c4b2d51b54225406d36b641f5e41bbc52a56612a8c6d14',
        '0x0000000000000000000000000000000000000000000000000000000000000001', // LAST 1
      ],
      // yNum
      [
        '0x4bda12f684bda12f684bda12f684bda12f684bda12f684bda12f684b8e38e23c',
        '0xc75e0c32d5cb7c0fa9d0a54b12a0a6d5647ab046d686da6fdffc90fc201d71a3',
        '0x29a6194691f91a73715209ef6512e576722830a201be2018a765e85a9ecee931',
        '0x2f684bda12f684bda12f684bda12f684bda12f684bda12f684bda12f38e38d84',
      ],
      // yDen
      [
        '0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffff93b',
        '0x7a06534bb8bdb49fd5e9e6632722c2989467c1bfc8e8d978dfb425d2685c2573',
        '0x6484aa716545ca2cf3a70c3fa8fe337e0a3d21162f0d6299a7bf8192bfd2a76f',
        '0x0000000000000000000000000000000000000000000000000000000000000001', // LAST 1
      ],
    ].map((i) => i.map((j) => BigInt(j))) as [bigint[], bigint[], bigint[], bigint[]]
  ))();
const mapSWU = /* @__PURE__ */ (() =>
  mapToCurveSimpleSWU(Fp, {
    A: BigInt('0x3f8731abdd661adca08a5558f0f5d272e953d363cb6f0e5d405447c01a444533'),
    B: BigInt('1771'),
    Z: Fp.create(BigInt('-11')),
  }))();
const htf = /* @__PURE__ */ (() =>
  createHasher(
    secp256k1.ProjectivePoint,
    (scalars: bigint[]) => {
      const { x, y } = mapSWU(Fp.create(scalars[0]));
      return isoMap(x, y);
    },
    {
      DST: 'secp256k1_XMD:SHA-256_SSWU_RO_',
      encodeDST: 'secp256k1_XMD:SHA-256_SSWU_NU_',
      p: Fp.ORDER,
      m: 1,
      k: 128,
      expand: 'xmd',
      hash: sha256,
    }
  ))();
export const hashToCurve = /* @__PURE__ */ (() => htf.hashToCurve)();
export const encodeToCurve = /* @__PURE__ */ (() => htf.encodeToCurve)();


function serializePoint(point: PointType<bigint>) {
  const data = new Uint8Array(33);
  const yBigInt = BigInt(point.y);
  data[0] = FpIsSquare(Fp)(yBigInt) ? 0x00 : 0x01;

  const xBigInt = BigInt(point.x);
  const xHex = xBigInt.toString(16).padStart(64, "0");
  const xBytes = Uint8Array.from(Buffer.from(xHex, "hex"));

  data.set(xBytes, 1);

  return data;
}

const borromeanHash = async (m: Uint8Array, e: Uint8Array, ridx: number, eidx: number) => {
  const ring = new Uint8Array(4);
  const epos = new Uint8Array(4);

  const writeBe32 = (buffer: Uint8Array, value: number) => {
    buffer[0] = (value >> 24) & 0xff;
    buffer[1] = (value >> 16) & 0xff;
    buffer[2] = (value >> 8) & 0xff;
    buffer[3] = value & 0xff;
  };

  writeBe32(ring, ridx);
  writeBe32(epos, eidx);

  const sha256Context = sha256.create();
  sha256Context.update(e);
  sha256Context.update(m);
  sha256Context.update(ring);
  sha256Context.update(epos);

  return sha256Context.digest();
}

function clz64(x: bigint) {
  if (x === 0n) return 64;
  let n = 0;
  while ((x & 0x8000000000000000n) === 0n) {
    x <<= 1n;
    n++;
  }
  return n;
}

type ProveParams = {
  rings: number,
  rsizes: number[],
  npub: number,
  secidx: number[],
  minValue: bigint,
  mantissa: number,
  scale: bigint,
  minBits: number,
  v: bigint,
  exp: number,
}

const rangeProveParams = (minBits: number, minValue: bigint, exp: number, value: bigint): ProveParams => {
  let i, v;
  let rsizes = new Array(32);
  let secidx = new Array(32);
  let rings = 1;
  rsizes[0] = 1;
  secidx[0] = 0;
  let scale = 1n;
  let mantissa = 0;
  let npub = 0;

  if (minValue === 0xffffffffffffffffn) exp = -1;

  if (exp >= 0) {
    let maxBits;
    let v2;
    if (
      (minValue && value > 0x7fffffffffffffffn) ||
      (value && minValue >= 0x7fffffffffffffffn)
    ) {
      throw new Error("value out of range");
    }
    maxBits = minValue ? clz64(BigInt(minValue)) : 64;
    if (minBits > maxBits) {
      minBits = maxBits;
    }
    if (minBits > 61 || value > 0x7fffffffffffffffn) {
      exp = 0;
    }
    v = value - BigInt(minValue);
    v2 = minBits ? 0xffffffffffffffffn >> BigInt(64 - minBits) : 0n;
    for (i = 0; i < exp && v2 <= 0xffffffffffffffffn / 10n; i++) {
      v /= 10n;
      v2 *= 10n;
    }
    exp = i;
    v2 = v;
    for (i = 0; i < exp; i++) {
      v2 *= 10n;
      scale *= 10n;
    }
    minValue = value - v2;
    mantissa = v ? 64 - clz64(v) : 1;
    if (minBits > mantissa) {
      mantissa = minBits;
    }
    rings = (mantissa + 1) >> 1;
    for (i = 0; i < rings; i++) {
      rsizes[i] = i < rings - 1 || !(mantissa & 1) ? 4 : 2;
      npub += rsizes[i];
      secidx[i] = Number((v >> BigInt(i * 2)) & 3n);
    }
    if (mantissa <= 0) throw new Error("Invalid mantissa value");
    if ((v & ~(0xffffffffffffffffn >> BigInt(64 - mantissa))) !== 0n)
      throw new Error("Did not get all the bits");
  } else {
    exp = 0;
    minValue = value;
    v = 0n;
    npub = 2;
  }

  if (v * scale + minValue !== value) throw new Error("Invalid value");
  if (rings <= 0 || rings > 32) throw new Error("Invalid number of rings");
  if (npub > 128) throw new Error("Invalid number of public keys");

  return {
    rings,
    rsizes,
    npub,
    secidx,
    minValue,
    mantissa,
    scale,
    minBits,
    v,
    exp,
  };
}

const borromeanSign = async (e0: Uint8Array, s: bigint[], pubs: PointType<bigint>[], k: bigint[], sec: bigint[], rsizes: number[], secidx: number[], nrings: number, m: Uint8Array) => {
  let rgej;
  let tmp = new Uint8Array(33);
  let count = 0;

  if (!e0 || !s || !pubs || !k || !sec || !rsizes || !secidx || !nrings || !m) {
    throw new Error("Invalid input");
  }

  const sha256_e0 = sha256.create();
  for (let i = 0; i < nrings; i++) {
    if (Number.MAX_SAFE_INTEGER - count < rsizes[i]) {
      throw new Error("Integer overflow");
    }

    rgej = Point.BASE.multiply(k[i]);
    if (rgej.equals(Point.ZERO)) {
      return 0;
    }

    tmp = rgej.toRawBytes(true);

    for (let j = secidx[i] + 1; j < rsizes[i]; j++) {
      tmp = await borromeanHash(m, tmp, i, j);
      let ens = bytesToNumberBE(tmp);
      if (ens >= secp256k1N) ens = ens % secp256k1N;

      rgej = pubs[count + j].multiply(ens).add(Point.BASE.multiply(s[count + j]));
      if (rgej.equals(Point.ZERO)) {
        return 0;
      }

      tmp = rgej.toRawBytes(true);
    }

    sha256_e0.update(tmp);
    count += rsizes[i];
  }

  sha256_e0.update(m);
  let digest = await sha256_e0.digest();
  e0.set(digest);

  count = 0;
  for (let i = 0; i < nrings; i++) {
    if (Number.MAX_SAFE_INTEGER - count < rsizes[i]) {
      throw new Error("Integer overflow");
    }

    tmp = await borromeanHash(m, e0.slice(0, 32), i, 0);
    let ens = bytesToNumberBE(tmp) % secp256k1N;

    if (ens === 0n || ens >= secp256k1N) {
      return 0;
    }

    for (let j = 0; j < secidx[i]; j++) {
      rgej = pubs[count + j].multiply(ens).add(Point.BASE.multiply(s[count + j]));

      if (rgej.equals(Point.ZERO)) {
        return 0;
      }

      tmp = rgej.toRawBytes(true);
      tmp = await borromeanHash(m, tmp, i, j + 1);
      ens = bytesToNumberBE(tmp) % secp256k1N;

      if (ens === 0n || ens >= secp256k1N) {
        return 0;
      }
    }

    s[count + secidx[i]] =
      (secp256k1N - ((ens * sec[i]) % secp256k1N) + k[i]) % secp256k1N;

    if (s[count + secidx[i]] === 0n) {
      return 0;
    }

    count += rsizes[i];
  }

  return 1;
}

const rangeproofPubExpand = (pubs: PointType<bigint>[], exp: number, rsizes: number[], rings: number, genp: string) => {
  var base = Point.fromHex(genp);
  var i, j, npub;
  if (exp < 0) {
    exp = 0;
  }

  base = base.negate();

  while (exp--) {
    var tmp = base.double();
    base = tmp.double().add(tmp);
  }

  npub = 0;
  for (i = 0; i < rings; i++) {
    for (j = 1; j < rsizes[i]; j++) {
      pubs[npub + j] = pubs[npub + j - 1].add(base);
    }
    if (i < rings - 1) {
      base = base.double().double();
    }
    npub += rsizes[i];
  }
}

export const rangeproofSign = async (
  minValue: bigint,
  commit: string,
  blind: string,
  nonce: string,
  exp: number,
  minBits: number,
  value: bigint,
  msg: string,
  extraCommit: string,
  genp: string,
) => {
  let proof = new Uint8Array(5134);
  let pubs = new Array(128);
  let s = new Array(128);
  let sec = new Array(32);
  let k = new Array(32);
  let sha256M = sha256.create();
  let prep = new Uint8Array(4096);
  let len;
  let i;

  let genP = Point.fromHex(genp);

  len = 0;
  if (minValue > value || minBits > 64 || minBits < 0 || exp < -1 || exp > 18) {
    return 0;
  }

  let v, rings, rsizes, npub, secidx, mantissa, scale;
  ({ v, rings, rsizes, npub, secidx, mantissa, scale, exp, minBits, minValue } = await rangeProveParams(minBits, minValue, exp, value));
  
  if (!v) return 0;

  proof[len] = (rsizes[0] > 1 ? 64 | exp : 0) | (minValue ? 32 : 0);
  len++;
  if (rsizes[0] > 1) {
    if (mantissa <= 0 || mantissa > 64) {
      throw new Error("Mantissa out of range");
    }
    proof[len] = mantissa - 1;
    len++;
  }
  if (minValue) {
    for (i = 0; i < 8; i++) {
      proof[len + i] = Number((minValue >> BigInt((7 - i) * 8)) & BigInt(255));
    }
    len += 8;
  }
  if (msg.length > 0 && msg.length > 128 * (rings - 1)) {
    return 0;
  }

  sha256M.update(ensureBytes('commit', commit));
  sha256M.update(serializePoint(genP));
  sha256M.update(proof.slice(0, len));

  prep.fill(0);
  if (msg != null) {
    prep.set(ensureBytes('msg', msg).slice(0, msg.length));
  }

  if (rsizes[rings - 1] > 1) {
    let idx = rsizes[rings - 1] - 1;
    idx -= Number(secidx[rings - 1] === idx);
    idx = ((rings - 1) * 4 + idx) * 32;
    for (i = 0; i < 8; i++) {
      let n = Number((v >> BigInt(56 - i * 8)) & BigInt(255));
      prep[8 + i + idx] = prep[16 + i + idx] = prep[24 + i + idx] = n;
      prep[i + idx] = 0;
    }
    prep[idx] = 128;
  }

  if (
    !(await rangeproofGenrand(
      sec,
      s,
      prep,
      rsizes,
      rings,
      nonce,
      commit,
      proof,
      len,
      genp,
    ))
  ) {
    return 0;
  }

  prep.fill(0);
  for (i = 0; i < rings; i++) {
    k[i] = s[i * 4 + secidx[i]];
    s[i * 4 + secidx[i]] = 0n;
  }

  let stmp = setScalarFromB32(ensureBytes('blind', blind));
  sec[rings - 1] = (sec[rings - 1] + stmp) % secp256k1N;

  let signs = new Uint8Array(proof.buffer, len, (rings + 6) >> 3);

  for (i = 0; i < (rings + 6) >> 3; i++) {
    signs[i] = 0;
    len++;
  }
  npub = 0;
  for (i = 0; i < rings; i++) {
    let val = (BigInt(secidx[i]) * scale) << BigInt(i * 2);
    let P1 = sec[i] ? Point.BASE.multiply(sec[i]) : Point.ZERO;
    let P2 = secidx[i] ? genP.multiply(val) : Point.ZERO;
    pubs[npub] = P1.add(P2);

    if (pubs[npub].equals(Point.ZERO)) return 0;

    if (i < rings - 1) {
      var tmpc = serializePoint(pubs[npub]);
      var quadness = tmpc[0];
      sha256M.update(tmpc);
      signs[i >> 3] |= quadness << (i & 7);
      proof.set(tmpc.slice(1), len);
      len += 32;
    }
    npub += rsizes[i];
  }

  rangeproofPubExpand(pubs, exp, rsizes, rings, genp);
  if (extraCommit != null) {
    sha256M.update(ensureBytes('extraCommit', extraCommit));
  }
  
  let signed = await borromeanSign(
    proof.subarray(len),
    s,
    pubs,
    k,
    sec,
    rsizes,
    secidx,
    rings,
    await sha256M.digest(),
  );

  if (!signed) return 0;

  len += 32;
  for (let i = 0; i < npub; i++) {
    proof.set(numTo32b(s[i]), len);
    len += 32;
  }

  proof = proof.slice(0, len);
  return proof;
}

let negateScalar = (a: bigint) => {
  if (a === 0n) {
    return 0n;
  }

  let result = secp256k1N - a;

  if (result < 0n) {
    result += secp256k1N;
  } else if (result >= secp256k1N) {
    result -= secp256k1N;
  }

  return result;
};

class RNG {
  private k: Uint8Array;
  private v: Uint8Array;
  private retry: boolean;

  constructor(k: Uint8Array, v: Uint8Array, retry = false) {
    this.k = k;
    this.v = v;
    this.retry = retry;
  }

  static async create(seed: Uint8Array): Promise<RNG> {
    const zero = new Uint8Array([0x00]);
    const one = new Uint8Array([0x01]);

    let v = new Uint8Array(32).fill(0x01); // RFC6979 3.2.b.
    let k = new Uint8Array(32).fill(0x00); // RFC6979 3.2.c.

    // RFC6979 3.2.d.
    k = hmac(sha256, k, concatBytes(v, zero, seed));
    v = hmac(sha256, k, v);

    // RFC6979 3.2.f.
    k = hmac(sha256, k, concatBytes(v, one, seed));
    v = hmac(sha256, k, v);

    return new RNG(k, v, false);
  }

  generate(outlen: number): Uint8Array {
    const zero = new Uint8Array([0x00]);
    let out = new Uint8Array(outlen);

    if (this.retry) {
      this.k = hmac(sha256, this.k, concatBytes(this.v, zero));
      this.v = hmac(sha256, this.k, this.v);
    }

    let remaining = outlen;
    let offset = 0;
    while (remaining > 0) {
      const now = Math.min(remaining, 32);
      this.v = hmac(sha256, this.k, this.v);
      out.set(this.v.slice(0, now), offset);
      remaining -= now;
      offset += now;
    }

    this.retry = true;
    return out;
  }

  finalize() {
    this.k.fill(0);
    this.v.fill(0);
    this.retry = false;
  }
}

async function rangeproofGenrand(
  sec: bigint[],
  s: bigint[],
  message: Uint8Array,
  rsizes: number[],
  rings: number,
  nonce: string,
  commit: string,
  proof: Uint8Array,
  len: number,
  gen: string,
) {
  let tmp = new Uint8Array(32);
  let rngseed = new Uint8Array(32 + 33 + 33 + len);
  let acc = 0n;
  let ret = 1;
  let npub = 0;

  if (len > 10) {
    throw new Error("Invalid length");
  }

  let slice = commit.slice(2);
  const genP = Point.fromHex(gen);
  const commitP = Point.fromHex("02" + slice);

  rngseed.set(ensureBytes('nonce', nonce).slice(0, 32), 0);
  rngseed.set(serializePoint(commitP), 32);
  rngseed.set(serializePoint(genP), 32 + 33);
  rngseed.set(proof.slice(0, len), 32 + 33 + 33);

  const rng = await RNG.create(rngseed);

  for (let i = 0; i < rings; i++) {
    if (i < rings - 1) {
      tmp = rng.generate(32);
      do {
        tmp = rng.generate(32);
        sec[i] = bytesToNumberBE(tmp) % secp256k1N;
      } while (bytesToNumberBE(tmp) > secp256k1N || sec[i] === 0n);
      acc = (acc + sec[i]) % secp256k1N;
    } else {
      sec[i] = negateScalar(acc);
    }

    for (let j = 0; j < rsizes[i]; j++) {
      tmp = rng.generate(32);
      if (message) {
        for (let b = 0; b < 32; b++) {
          tmp[b] ^= message[(i * 4 + j) * 32 + b];
          message[(i * 4 + j) * 32 + b] = tmp[b];
        }
      }
      s[npub] = bytesToNumberBE(tmp) % secp256k1N;
      ret &= Number(s[npub] !== 0n);
      npub++;
    }
  }
  acc = 0n;

  return ret;
}


const setScalarFromB32 = (b32: Uint8Array) => {
  if (b32.length !== 32) {
    throw new Error("Input must be a 32-byte array");
  }

  const d0 = bytesToNumberBE(b32.slice(24, 32));
  const d1 = bytesToNumberBE(b32.slice(16, 24));
  const d2 = bytesToNumberBE(b32.slice(8, 16));
  const d3 = bytesToNumberBE(b32.slice(0, 8));

  let scalar = (d3 << 192n) | (d2 << 128n) | (d1 << 64n) | d0;

  if (scalar >= secp256k1N) {
    scalar -= secp256k1N;
  }

  return scalar;
};
