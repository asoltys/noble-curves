import { readFileSync } from 'node:fs';
import { mark, run } from 'micro-bmark';
import { bls12_381 as bls } from '../bls12-381.js';
import { dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
const __dirname = dirname(fileURLToPath(import.meta.url));
const G2_VECTORS = readFileSync(
  `${__dirname}/../test/bls12-381/bls12-381-g2-test-vectors.txt`,
  'utf-8'
)
  .trim()
  .split('\n')
  .map((l) => l.split(':'));

run(async () => {
  console.log(`\x1b[36mbls12-381\x1b[0m`);
  let p1, p2, sig;
  await mark('init', 1, () => {
    p1 =
      bls.G1.ProjectivePoint.BASE.multiply(
        0x28b90deaf189015d3a325908c5e0e4bf00f84f7e639b056ff82d7e70b6eede4cn
      );
    p2 =
      bls.G2.ProjectivePoint.BASE.multiply(
        0x28b90deaf189015d3a325908c5e0e4bf00f84f7e639b056ff82d7e70b6eede4dn
      );
    bls.pairing(p1, p2);
  });
  const priv = '28b90deaf189015d3a325908c5e0e4bf00f84f7e639b056ff82d7e70b6eede4c';
  sig = bls.sign('09', priv);
  const pubs = G2_VECTORS.map((v) => bls.getPublicKey(v[0]));
  const sigs = G2_VECTORS.map((v) => v[2]);
  const pub = bls.getPublicKey(priv);
  const pub512 = pubs.slice(0, 512); // .map(bls.PointG1.fromHex)
  const pub32 = pub512.slice(0, 32);
  const pub128 = pub512.slice(0, 128);
  const pub2048 = pub512.concat(pub512, pub512, pub512);
  const sig512 = sigs.slice(0, 512); // .map(bls.PointG2.fromSignature);
  const sig32 = sig512.slice(0, 32);
  const sig128 = sig512.slice(0, 128);
  const sig2048 = sig512.concat(sig512, sig512, sig512);
  await mark('getPublicKey 1-bit', 1000, () => bls.getPublicKey('2'.padStart(64, '0')));
  await mark('getPublicKey', 1000, () => bls.getPublicKey(priv));
  await mark('sign', 50, () => bls.sign('09', priv));
  await mark('verify', 50, () => bls.verify(sig, '09', pub));
  await mark('pairing', 100, () => bls.pairing(p1, p2));

  const scalars1 = Array(4096)
    .fill(0)
    .map((i) => 2n ** 235n - BigInt(i));
  const scalars2 = Array(4096)
    .fill(0)
    .map((i) => 2n ** 241n + BigInt(i));
  const points = scalars1.map((s) => bls.G1.ProjectivePoint.BASE.multiply(s));
  const pointsG2 = scalars1.map((s) => bls.G2.ProjectivePoint.BASE.multiply(s));

  const pairingBatch = 10;
  await mark(`pairing${pairingBatch}`, 10, () => {
    const res = [];
    for (let i = 0; i < pairingBatch; i++) res.push({ g1: points[i], g2: pointsG2[i] });
    bls.pairingBatch(res);
  });

  await mark('MSM 4096 scalars x points', 1, () => {
    // naive approach, not using multi-scalar-multiplication
    let sum = bls.G1.ProjectivePoint.ZERO;
    for (let i = 0; i < 4096; i++) {
      const scalar = scalars2[i];
      const G1 = points[i];
      const mutliplied = G1.multiplyUnsafe(scalar);
      sum = sum.add(mutliplied);
    }
  });

  await mark('aggregatePublicKeys/8', 100, () => bls.aggregatePublicKeys(pubs.slice(0, 8)));
  await mark('aggregatePublicKeys/32', 50, () => bls.aggregatePublicKeys(pub32));
  await mark('aggregatePublicKeys/128', 20, () => bls.aggregatePublicKeys(pub128));
  await mark('aggregatePublicKeys/512', 10, () => bls.aggregatePublicKeys(pub512));
  await mark('aggregatePublicKeys/2048', 5, () => bls.aggregatePublicKeys(pub2048));
  await mark('aggregateSignatures/8', 100, () => bls.aggregateSignatures(sigs.slice(0, 8)));
  await mark('aggregateSignatures/32', 50, () => bls.aggregateSignatures(sig32));
  await mark('aggregateSignatures/128', 20, () => bls.aggregateSignatures(sig128));
  await mark('aggregateSignatures/512', 10, () => bls.aggregateSignatures(sig512));
  await mark('aggregateSignatures/2048', 5, () => bls.aggregateSignatures(sig2048));
});
