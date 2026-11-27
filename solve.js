// solve.js — the entry: a faster drop-in for makefun-diff 1.0.0.
//
// The diff itself runs in diff.wasm (compiled from diff.ts, the
// AssemblyScript source in this repository): it hashes and interns lines
// without materialising substrings, pins the diff on blocks of consecutive
// lines unique in both texts, solves only the small gaps with the exact
// Myers search (deletion-on-tie, no edge pruning, snake after every step),
// and writes the patch straight into the output buffer. The batch entry
// point even parses the harness's cases.json itself, so no JSON.parse,
// stringify, or encoder round-trip sits on the timed path.
//
// run(input) answers one case, exactly as makefun-diff does, and returns
// the patch string. runBatch(bytes) answers a whole cases.json buffer and
// returns the answers.json bytes. Both answer each case alone, from that
// case's bytes only; nothing is cached from one case to the next. Paths are
// resolved from import.meta.url, never from the working directory.

import { readFileSync } from 'node:fs';

const wasmBytes = readFileSync(new URL('./diff.wasm', import.meta.url));
const { instance } = await WebAssembly.instantiate(wasmBytes, {});
const memory = instance.exports.memory;
const wasmRunBatch = instance.exports.runBatch;
const wasmRunCase = instance.exports.runCase;

// The module's own static data lives at low addresses; inputs start here.
const INPUT_BASE = 65536;
const te = new TextEncoder();
const td = new TextDecoder();

function ensureMemory(bytes) {
  const pages = Math.ceil(bytes / 65536);
  const cur = memory.buffer.byteLength / 65536;
  if (pages > cur) memory.grow(pages - cur);
}

// Heap headroom reserved in one growth step: the WASM core's bump heap
// grows itself, but every growth step can copy the memory it already
// holds, so growing once up front is far cheaper than growing a little
// at a time. 128 MiB covers the per-case tables and the worst-case Myers
// rows for this generator's cases, with room to spare.
const HEAP_RESERVE = 128 * 1024 * 1024;

function align8(n) {
  return (n + 7) & ~7;
}

/** makefun-diff 1.0.0's answer for one case's input, as a string. */
export function run(input) {
  if (input === null || typeof input !== 'object' || typeof input.old !== 'string' || typeof input.new !== 'string') {
    throw new TypeError('makefun-diff: the input is { old, new }, two strings');
  }
  // UTF-8 is at most 3 bytes per UTF-16 code unit, so these regions always fit.
  const oldCap = input.old.length * 3 + 8;
  const newCap = input.new.length * 3 + 8;
  const oldPtr = INPUT_BASE;
  const newPtr = align8(oldPtr + oldCap);
  const outPtr = align8(newPtr + newCap);
  const outCap = (oldCap + newCap) * 4 + 1024;
  const heapBase = align8(outPtr + outCap);
  ensureMemory(heapBase + HEAP_RESERVE);
  const mem = new Uint8Array(memory.buffer);
  const oldLen = te.encodeInto(input.old, mem.subarray(oldPtr, oldPtr + oldCap)).written;
  const newLen = te.encodeInto(input.new, mem.subarray(newPtr, newPtr + newCap)).written;
  const outLen = wasmRunCase(oldPtr, oldLen, newPtr, newLen, outPtr, heapBase);
  if (outLen < 0) throw new Error('diff: the WASM core failed on this case');
  return td.decode(new Uint8Array(memory.buffer, outPtr, outLen));
}

/**
 * Answer a whole cases.json buffer (a Uint8Array of the file's bytes) and
 * return the answers.json bytes as a Uint8Array view of the WASM memory.
 * The caller should consume it (e.g. write it out) before the next call.
 */
export function runBatch(buf) {
  const jsonLen = buf.length;
  const jsonPtr = INPUT_BASE;
  const outPtr = align8(jsonPtr + jsonLen);
  const outCap = jsonLen * 4 + 1048576;
  const heapBase = align8(outPtr + outCap);
  ensureMemory(heapBase + HEAP_RESERVE);
  const mem = new Uint8Array(memory.buffer);
  mem.set(buf, jsonPtr);
  const outLen = wasmRunBatch(jsonPtr, jsonLen, outPtr, heapBase);
  if (outLen < 0) throw new Error('diff: the WASM core failed on this batch');
  return new Uint8Array(memory.buffer, outPtr, outLen);
}
