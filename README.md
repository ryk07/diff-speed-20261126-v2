# Diff two texts faster (make.fun diff-speed-01-run-20261126)

[![make.fun · diff-speed-01-run-20261126](https://make.fun/badge/diff-speed-01-run-20261126.svg)](https://make.fun/bounty/diff-speed-01-run-20261126?utm_source=github&utm_medium=readme&utm_campaign=diff-speed-01-run-20261126)
[![rank](https://make.fun/badge/diff-speed-01-run-20261126/ryk07/diff-speed-20261126-v2/rank.svg)](https://make.fun/bounty/diff-speed-01-run-20261126/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=diff-speed-01-run-20261126)
[![reward](https://make.fun/badge/diff-speed-01-run-20261126/ryk07/diff-speed-20261126-v2/reward.svg)](https://make.fun/bounty/diff-speed-01-run-20261126?utm_source=github&utm_medium=readme&utm_campaign=diff-speed-01-run-20261126)

A fast drop-in replacement for `makefun-diff` 1.0.0: it returns exactly the
same patch string for `{old, new}`, but several times faster than the house
baseline on the practice set. The whole diff runs in one small WASM module
(`diff.wasm`, compiled from the AssemblyScript source `diff.ts` in this
repository), over raw UTF-8 bytes, and the batch entry point even parses
the harness's `cases.json` itself, so no `JSON.parse`, stringify, or
encoder round-trip sits on the timed path.

## How it works

Most of a 20,000–40,000 line text is unchanged, so the diff is pinned on
**anchors**: blocks of consecutive lines that are unique in both texts (a
run of 2 or more such lines is almost always part of the minimal edit
script). Only the small gaps between anchors are solved with the exact
Myers search (same tie-break as the reference: deletion-preferred, no edge
pruning, snake after every step). Four cheap filters drop anchors that sit
on a moved or swapped block, where the reference's greedy tie-break keeps
the old-first block instead:

- a **swap signature** (the line just outside the block matches the line
  just inside it on the other side),
- a **diagonal-offset** check (a moved block's anchors sit far off the
  diagonal of the anchors a fixed distance away on both sides),
- a **large-gap** check (an anchor next to a change of more than 16 lines
  sits at the boundary of a rearrangement),
- a **crossing** check (an anchor crossed by another unique block that is
  old-first and nearby is the old-second block of a swap).

Dropping an anchor is always safe — the gap Myers is exact — so the result
is byte-identical to the reference. If no anchor survives, the entry falls
back to the exact Myers search over the whole middle region.

Lines are hashed (SIMD128, one multiply per 16 bytes) and interned to
integer ids in an open-addressing table — a hash match is always confirmed
by memcmp, so the ids are exact — with no substrings ever materialised.
The patch is written straight into the output buffer (bulk copies for
clean line interiors, JSON escaping only where a byte needs it), and the
batch path parses `cases.json` with a SIMD scan for backslashes and
quotes, unescaping into the module's heap.

## Verification

- Practice set: 4/4 outputs byte-identical to `practice/reference/expected.json`.
- 60 generated cases (kit's own generator, one seed) plus 12 fresh cases
  from three new seeds: 72/72 byte-identical to the reference `diffPatch`.
- Deterministic: running `main.ts` twice from different working
  directories produces byte-identical `answers.json`.

## Layout

- `diff.ts` — the WASM core's source (AssemblyScript). Build it with
  `asc diff.ts --outFile diff.wasm --runtime stub --optimize -O3 --enable simd`.
- `diff.wasm` — the compiled module, built from `diff.ts` and committed.
- `solve.js` — the entry: `export function run(input)` returns the patch
  string for `{old, new}`, and `export function runBatch(buf)` answers a
  whole `cases.json` buffer. Node 22, stdlib only, no dependencies.
- `main.ts` — the harness driver (reads `/input/cases.json`, writes
  `/output/answers.json`).
- `package.json` — `{"type": "module"}`.
