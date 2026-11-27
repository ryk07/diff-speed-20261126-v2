// The harness driver: the harness runs `node /bot/main.ts` (node22). It
// reads every case from /input/cases.json and writes /output/answers.json:
// a JSON array of the answers, one per case and in the cases' order.
// Outside a container MAKEFUN_INPUT_DIR and MAKEFUN_OUTPUT_DIR stand in
// for /input and /output.
//
// The answers come from solve.js's runBatch, which hands the raw file
// bytes to the WASM core: the core parses the cases, answers each case
// alone (nothing is cached from one case to the next), and writes the
// answers.json bytes. That keeps JSON.parse, stringify, and the encoder
// round-trip off the timed path; solve.js's run() still answers a single
// case on its own, and is what the local validation uses.

import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

/** solve.js, imported by its URL (a .js module carries no types). */
const { runBatch } = (await import(new URL('./solve.js', import.meta.url).href)) as {
  runBatch: (buf: Uint8Array) => Uint8Array;
};

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const raw = readFileSync(join(INPUT_DIR, 'cases.json'));
const answers = runBatch(raw);
writeFileSync(join(OUTPUT_DIR, 'answers.json'), answers);
