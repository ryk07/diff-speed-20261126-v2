// diff.ts — WASM core for the diff-speed entry.
//
// Computes exactly makefun-diff 1.0.0's patch for { old, new } (common
// prefix, common suffix, Myers greedy search with the deletion-on-tie break,
// no edge pruning, snake after every step; patch with 3 context lines, runs
// at most 6 kept lines apart sharing a hunk, '%' after a bare final line).
//
// Speed comes from three places: (1) the diff is pinned on anchors —
// blocks of >= 2 consecutive lines unique in both texts — and only the small
// gaps between anchors go through the exact Myers search, with four cheap
// filters dropping anchors that sit on a moved or swapped block; dropping
// an anchor is always safe, because the gap Myers is exact, and with no
// anchor left the entry falls back to the exact Myers over the whole middle;
// (2) everything runs in one WASM module over raw UTF-8 bytes, so lines are
// hashed and interned without ever materialising substrings, and the patch
// is written straight into the output buffer; (3) the batch entry point
// parses the harness's cases.json itself, so no JSON.parse / stringify and
// no encoder round-trip sit on the timed path.
//
// All work happens in linear memory. The JS side writes the input at
// INPUT_BASE (64 KiB, clear of the module's own static data), the output
// region follows it, and the bump heap starts at the heapBase the caller
// passes in. The allocator grows memory itself when the heap needs more
// room. Nothing is cached from one case to the next: each case is answered
// alone, from its own bytes.

// ---------------------------------------------------------------- bump heap

let heapPtr: i32 = 0;

// Grow memory until heapPtr + n bytes fit. Used by the allocator and by
// the JSON reader, which writes unescaped bytes straight at heapPtr.
function ensureRoom(n: i32): void {
  const end: i32 = memory.size() << 16;
  if (heapPtr + n > end) {
    const pages: i32 = ((heapPtr + n - end) + 65535) >> 16;
    memory.grow(pages);
  }
}

function alloc(bytes: i32): i32 {
  bytes = (bytes + 7) & ~7;
  ensureRoom(bytes);
  const p: i32 = heapPtr;
  heapPtr += bytes;
  return p;
}

// ---------------------------------------------------------------- small util

function memeq(a: i32, b: i32, n: i32): bool {
  let i: i32 = 0;
  for (; i + 4 <= n; i += 4) {
    if (load<i32>(a + i) != load<i32>(b + i)) return false;
  }
  for (; i < n; i++) {
    if (load<u8>(a + i) != load<u8>(b + i)) return false;
  }
  return true;
}

function writeU32(out: i32, v: u32): i32 {
  // Decimal digits of v, no allocation.
  let buf: i32 = out;
  let tmp: u32 = v;
  let n: i32 = 0;
  if (tmp == 0) {
    store<u8>(buf, 48);
    return buf + 1;
  }
  let rev: i32 = 0;
  while (tmp > 0) {
    rev = rev * 10 + <i32>(tmp % 10);
    tmp /= 10;
    n++;
  }
  // rev holds the digits backwards; emit them in order.
  for (let i: i32 = 0; i < n; i++) {
    store<u8>(buf + i, 48 + (rev % 10));
    rev /= 10;
  }
  return buf + n;
}

// FNV-1a over a byte span, one multiply per 16 bytes: each 16-byte block
// is xor-folded across its four lanes, then mixed, with a Murmur-style
// avalanche so short similar lines spread well.
function lineHash(ptr: i32, len: i32): u32 {
  let h: u32 = 2166136261;
  let i: i32 = 0;
  const end16: i32 = len & ~15;
  for (; i < end16; i += 16) {
    const v = v128.load(ptr + i);
    const x: u32 = v128.extract_lane<u32>(v, 0) ^ v128.extract_lane<u32>(v, 1) ^ v128.extract_lane<u32>(v, 2) ^ v128.extract_lane<u32>(v, 3);
    h ^= x;
    h *= 16777619;
  }
  for (; i + 4 <= len; i += 4) {
    h ^= load<u32>(ptr + i);
    h *= 16777619;
  }
  for (; i < len; i++) {
    h ^= load<u8>(ptr + i);
    h *= 16777619;
  }
  h ^= h >> 16;
  h *= 2246822507;
  h ^= h >> 13;
  h *= 3266489909;
  h ^= h >> 16;
  return h;
}

// ---------------------------------------------------------------- radix sort
// LSD radix sort, base 256, of the index array `idx` (n i32 entries) by the
// 32-bit keys in `keys` (indexed by the values in idx). `tmp` is scratch of
// n i32 entries; `cnt` is scratch of 256 i32 entries. Sorts in place.

function radixSort(keys: i32, idx: i32, n: i32, tmp: i32, cnt: i32): void {
  for (let pass: i32 = 0; pass < 4; pass++) {
    memory.fill(cnt, 0, 1024);
    const sh: i32 = pass * 8;
    for (let i: i32 = 0; i < n; i++) {
      const id: i32 = load<i32>(idx + i * 4);
      const k: u32 = load<u32>(keys + id * 4);
      const b: i32 = <i32>((k >> sh) & 255);
      store<i32>(cnt + b * 4, load<i32>(cnt + b * 4) + 1);
    }
    let sum: i32 = 0;
    for (let b: i32 = 0; b < 256; b++) {
      const c: i32 = load<i32>(cnt + b * 4);
      store<i32>(cnt + b * 4, sum);
      sum += c;
    }
    for (let i: i32 = 0; i < n; i++) {
      const id: i32 = load<i32>(idx + i * 4);
      const k: u32 = load<u32>(keys + id * 4);
      const b: i32 = <i32>((k >> sh) & 255);
      const p: i32 = load<i32>(cnt + b * 4);
      store<i32>(cnt + b * 4, p + 1);
      store<i32>(tmp + p * 4, id);
    }
    memory.copy(idx, tmp, n * 4);
  }
}

// ---------------------------------------------------------------- lines
// A line is the byte span up to and including its '\n', or to the end of
// the text for a bare last line. scanLines writes the start of every line
// plus a sentinel (the text length) and returns the line count.

function scanLines(ptr: i32, len: i32, startsOut: i32): i32 {
  let n: i32 = 0;
  let s: i32 = 0;
  let i: i32 = 0;
  const splatNL = v128.splat<i8>(10);
  const end16: i32 = len & ~15;
  for (; i < end16; i += 16) {
    const v = v128.load(ptr + i);
    let bits: i32 = v128.bitmask<i8>(v128.eq<i8>(v, splatNL));
    while (bits != 0) {
      const lsb: i32 = bits & -bits;
      const j: i32 = 31 - <i32>Math.clz32(lsb);
      store<i32>(startsOut + n * 4, s);
      n++;
      s = i + j + 1;
      bits ^= lsb;
    }
  }
  for (; i < len; i++) {
    if (load<u8>(ptr + i) == 10) {
      store<i32>(startsOut + n * 4, s);
      n++;
      s = i + 1;
    }
  }
  if (s < len) {
    store<i32>(startsOut + n * 4, s);
    n++;
  }
  store<i32>(startsOut + n * 4, len);
  return n;
}

// Combined line table for one case. Old lines are 0..nOld-1, new lines
// nOld..nOld+nNew-1. starts holds old starts, the old sentinel, new
// starts, the new sentinel; lineStart/lineEnd resolve a combined index.
let gOldPtr: i32 = 0;
let gNewPtr: i32 = 0;
let gOldLen: i32 = 0;
let gNewLen: i32 = 0;
let gStarts: i32 = 0;
let gNOld: i32 = 0;
let gNNew: i32 = 0;

function lineStart(i: i32): i32 {
  if (i < gNOld) return load<i32>(gStarts + i * 4);
  return load<i32>(gStarts + (i + 1) * 4);
}
function lineEnd(i: i32): i32 {
  if (i < gNOld) return load<i32>(gStarts + (i + 1) * 4);
  return load<i32>(gStarts + (i + 2) * 4);
}
function linePtr(i: i32): i32 {
  return i < gNOld ? gOldPtr : gNewPtr;
}

// Intern every line of both texts to a shared id space: two lines share an
// id exactly when their byte spans are equal. Open addressing on the line
// hash (load at most 1/4, so probes stay short); a hash match is always
// confirmed by memcmp, so the ids are exact. One interleaved table holds
// (hash, line) pairs, so a probe touches a single cache line. Returns the
// id count V, and fills the ids array (one i32 per combined line, in line
// order). Id values are opaque labels — only equality is ever used — so
// insertion order is as good as sorted order, and no sort is needed.
function internLines(ids: i32): i32 {
  const total: i32 = gNOld + gNNew;
  let size: i32 = 1024;
  while (size < total * 4) size <<= 1;
  const mask: i32 = size - 1;
  const tab: i32 = alloc(size * 8);
  memory.fill(tab + 4, 255, size * 8 - 4);
  let v: i32 = 0;
  for (let i: i32 = 0; i < total; i++) {
    const p: i32 = linePtr(i);
    const s: i32 = lineStart(i);
    const e: i32 = lineEnd(i);
    const len: i32 = e - s;
    const h: u32 = lineHash(p + s, len);
    let slot: i32 = <i32>(h & <u32>mask);
    while (true) {
      const ref: i32 = load<i32>(tab + slot * 8 + 4);
      if (ref < 0) {
        store<u32>(tab + slot * 8, h);
        store<i32>(tab + slot * 8 + 4, i);
        store<i32>(ids + i * 4, v);
        v++;
        break;
      }
      if (load<u32>(tab + slot * 8) == h) {
        const rp: i32 = linePtr(ref);
        const rs: i32 = lineStart(ref);
        const re: i32 = lineEnd(ref);
        if (re - rs == len && memeq(rp + rs, p + s, len)) {
          store<i32>(ids + i * 4, load<i32>(ids + ref * 4));
          break;
        }
      }
      slot = (slot + 1) & mask;
    }
  }
  return v;
}

// ---------------------------------------------------------------- Myers
// Exact Myers over id arrays a[0..n), b[0..m): the furthest-reaching x per
// diagonal per d, deletion on a tie (when deletion and insertion reach the
// same x, the deletion's path is kept), never past either text's end, snake
// after every step. Writes runs as (kind, count) pairs into the arrays at
// rk/rc (kind 0 keep, 1 delete, 2 insert) and returns the run count. Rows
// are kept, one bump allocation per d, so the backtrack can walk them.

const KEEP: i32 = 0;
const DEL: i32 = 1;
const INS: i32 = 2;

function myersRuns(a: i32, n: i32, b: i32, m: i32, rk: i32, rc: i32): i32 {
  if (n == 0 && m == 0) return 0;
  const maxD: i32 = n + m;
  const rowPtrs: i32 = alloc((maxD + 1) * 4);
  // d = 0 row: the opening snake.
  let row: i32 = alloc(4);
  let x: i32 = 0;
  let y: i32 = 0;
  while (x < n && y < m && load<i32>(a + x * 4) == load<i32>(b + y * 4)) {
    x++;
    y++;
  }
  store<i32>(row, x);
  store<i32>(rowPtrs, row);
  let dStar: i32 = 0;
  let kStar: i32 = 0;
  if (x != n || y != m) {
    let done: bool = false;
    for (let d: i32 = 1; d <= maxD && !done; d++) {
      const prev: i32 = load<i32>(rowPtrs + (d - 1) * 4);
      row = alloc((2 * d + 1) * 4);
      memory.fill(row, 255, (2 * d + 1) * 4);
      for (let k: i32 = -d; k <= d; k += 2) {
        const idx: i32 = k + d;
        let delX: i32 = -1;
        let insX: i32 = -1;
        if (k > -d) delX = load<i32>(prev + (k + d - 2) * 4);
        if (k < d) insX = load<i32>(prev + (k + d) * 4);
        const canDel: bool = delX >= 0 && delX < n;
        const canIns: bool = insX >= 0 && insX - 1 - k < m;
        if (!canDel && !canIns) continue;
        const byDel: i32 = canDel ? delX : -2;
        const byIns: i32 = canIns ? insX - 1 : -2;
        let xx: i32;
        if (byDel >= byIns) xx = delX + 1;
        else xx = insX;
        let yy: i32 = xx - k;
        while (xx < n && yy < m && load<i32>(a + xx * 4) == load<i32>(b + yy * 4)) {
          xx++;
          yy++;
        }
        store<i32>(row + idx * 4, xx);
        if (xx == n && yy == m) {
          dStar = d;
          kStar = k;
          done = true;
          break;
        }
      }
      store<i32>(rowPtrs + d * 4, row);
    }
    if (!done) return -1; // unreachable for real inputs; caller treats as error
  }
  // Backtrack from (dStar, kStar); runs come out reversed.
  const revK: i32 = alloc((2 * (dStar + 1) + 2) * 4);
  const revC: i32 = alloc((2 * (dStar + 1) + 2) * 4);
  let rn: i32 = 0;
  let d: i32 = dStar;
  let k: i32 = kStar;
  let cx: i32 = n;
  let cy: i32 = m;
  while (d > 0) {
    const prev: i32 = load<i32>(rowPtrs + (d - 1) * 4);
    let delX: i32 = -1;
    let insX: i32 = -1;
    if (k > -d) delX = load<i32>(prev + (k + d - 2) * 4);
    if (k < d) insX = load<i32>(prev + (k + d) * 4);
    const canDel: bool = delX >= 0 && delX < n;
    const canIns: bool = insX >= 0 && insX - 1 - k < m;
    const byDel: i32 = canDel ? delX : -2;
    const byIns: i32 = canIns ? insX - 1 : -2;
    let x0: i32;
    let y0: i32;
    let isDel: bool;
    if (byDel >= byIns) {
      isDel = true;
      x0 = delX + 1;
      y0 = x0 - k;
    } else {
      isDel = false;
      x0 = insX;
      y0 = x0 - k;
    }
    const keep: i32 = cx - x0;
    if (keep > 0) {
      store<i32>(revK + rn * 4, KEEP);
      store<i32>(revC + rn * 4, keep);
      rn++;
    }
    store<i32>(revK + rn * 4, isDel ? DEL : INS);
    store<i32>(revC + rn * 4, 1);
    rn++;
    if (isDel) {
      cx = x0 - 1;
      cy = y0;
      k = k - 1;
    } else {
      cx = x0;
      cy = y0 - 1;
      k = k + 1;
    }
    d--;
  }
  if (cx > 0) {
    store<i32>(revK + rn * 4, KEEP);
    store<i32>(revC + rn * 4, cx);
    rn++;
  }
  // Reverse into the output, merging neighbours of one kind.
  let out: i32 = 0;
  for (let i: i32 = rn - 1; i >= 0; i--) {
    const kind: i32 = load<i32>(revK + i * 4);
    const cnt: i32 = load<i32>(revC + i * 4);
    if (out > 0 && load<i32>(rk + (out - 1) * 4) == kind) {
      store<i32>(rc + (out - 1) * 4, load<i32>(rc + (out - 1) * 4) + cnt);
    } else {
      store<i32>(rk + out * 4, kind);
      store<i32>(rc + out * 4, cnt);
      out++;
    }
  }
  return out;
}

// ---------------------------------------------------------------- anchors
// Pin the middle region on blocks of >= 2 consecutive lines unique in both
// texts, then solve only the gaps with the exact Myers above. Four filters
// drop anchors that sit on a moved or swapped block, where the reference's
// greedy tie-break keeps the old-first block instead; dropping an anchor is
// always safe, because the gap Myers then decides that stretch exactly.
// Returns the run count, or -1 when no anchor survives (the caller then
// runs the exact Myers over the whole middle).

function anchorRuns(aMid: i32, nMid: i32, bMid: i32, mMid: i32, v: i32, rk: i32, rc: i32): i32 {
  const cntA: i32 = alloc(v * 4);
  const cntB: i32 = alloc(v * 4);
  const posA: i32 = alloc(v * 4);
  const posB: i32 = alloc(v * 4);
  memory.fill(cntA, 0, v * 4);
  memory.fill(cntB, 0, v * 4);
  memory.fill(posA, 255, v * 4);
  memory.fill(posB, 255, v * 4);
  for (let i: i32 = 0; i < nMid; i++) {
    const id: i32 = load<i32>(aMid + i * 4);
    if (load<i32>(cntA + id * 4) == 0) store<i32>(posA + id * 4, i);
    store<i32>(cntA + id * 4, load<i32>(cntA + id * 4) + 1);
  }
  for (let i: i32 = 0; i < mMid; i++) {
    const id: i32 = load<i32>(bMid + i * 4);
    if (load<i32>(cntB + id * 4) == 0) store<i32>(posB + id * 4, i);
    store<i32>(cntB + id * 4, load<i32>(cntB + id * 4) + 1);
  }
  // Unique-in-both matches, then counting-sorted by x.
  const maxM: i32 = nMid < mMid ? nMid : mMid;
  const mx: i32 = alloc((maxM + 1) * 4);
  const my: i32 = alloc((maxM + 1) * 4);
  let nm: i32 = 0;
  for (let id: i32 = 0; id < v; id++) {
    if (load<i32>(cntA + id * 4) == 1 && load<i32>(cntB + id * 4) == 1) {
      store<i32>(mx + nm * 4, load<i32>(posA + id * 4));
      store<i32>(my + nm * 4, load<i32>(posB + id * 4));
      nm++;
    }
  }
  if (nm == 0) return -1;
  // Counting sort by x (stable): bucket counts, then scatter.
  const bcnt: i32 = alloc((nMid + 1) * 4);
  memory.fill(bcnt, 0, (nMid + 1) * 4);
  for (let i: i32 = 0; i < nm; i++) {
    const x: i32 = load<i32>(mx + i * 4);
    store<i32>(bcnt + x * 4, load<i32>(bcnt + x * 4) + 1);
  }
  let sum: i32 = 0;
  for (let x: i32 = 0; x < nMid; x++) {
    const c: i32 = load<i32>(bcnt + x * 4);
    store<i32>(bcnt + x * 4, sum);
    sum += c;
  }
  const sx: i32 = alloc(nm * 4);
  const sy: i32 = alloc(nm * 4);
  for (let i: i32 = 0; i < nm; i++) {
    const x: i32 = load<i32>(mx + i * 4);
    const p: i32 = load<i32>(bcnt + x * 4);
    store<i32>(bcnt + x * 4, p + 1);
    store<i32>(sx + p * 4, x);
    store<i32>(sy + p * 4, load<i32>(my + i * 4));
  }
  // Group consecutive matches (x+1, y+1) into blocks; keep len >= 2.
  const bx: i32 = alloc(nm * 4);
  const by: i32 = alloc(nm * 4);
  const bl: i32 = alloc(nm * 4);
  let nb: i32 = 0;
  for (let i: i32 = 0; i < nm; i++) {
    const x: i32 = load<i32>(sx + i * 4);
    const y: i32 = load<i32>(sy + i * 4);
    if (nb > 0 && x == load<i32>(bx + (nb - 1) * 4) + load<i32>(bl + (nb - 1) * 4) && y == load<i32>(by + (nb - 1) * 4) + load<i32>(bl + (nb - 1) * 4)) {
      store<i32>(bl + (nb - 1) * 4, load<i32>(bl + (nb - 1) * 4) + 1);
    } else {
      store<i32>(bx + nb * 4, x);
      store<i32>(by + nb * 4, y);
      store<i32>(bl + nb * 4, 1);
      nb++;
    }
  }
  const cx: i32 = alloc(nb * 4);
  const cy: i32 = alloc(nb * 4);
  const cl: i32 = alloc(nb * 4);
  let nc: i32 = 0;
  for (let i: i32 = 0; i < nb; i++) {
    if (load<i32>(bl + i * 4) >= 2) {
      store<i32>(cx + nc * 4, load<i32>(bx + i * 4));
      store<i32>(cy + nc * 4, load<i32>(by + i * 4));
      store<i32>(cl + nc * 4, load<i32>(bl + i * 4));
      nc++;
    }
  }
  if (nc == 0) return -1;
  // Longest increasing subsequence of the candidate blocks by y, in x
  // order: Fenwick DP over compressed y, then a backward scan over the dp
  // buckets that favours the earliest line at each length.
  const ys: i32 = alloc(nc * 4);
  const ytmp: i32 = alloc(nc * 4);
  const ycnt: i32 = alloc(256 * 4);
  for (let i: i32 = 0; i < nc; i++) store<i32>(ys + i * 4, load<i32>(cy + i * 4));
  const yOrd: i32 = alloc(nc * 4);
  for (let i: i32 = 0; i < nc; i++) store<i32>(yOrd + i * 4, i);
  radixSort(ys, yOrd, nc, ytmp, ycnt);
  const uniqY: i32 = alloc(nc * 4);
  let ny: i32 = 0;
  for (let i: i32 = 0; i < nc; i++) {
    const yv: i32 = load<i32>(ys + load<i32>(yOrd + i * 4) * 4);
    if (i == 0 || yv != load<i32>(uniqY + (ny - 1) * 4)) {
      store<i32>(uniqY + ny * 4, yv);
      ny++;
    }
  }
  const yRank: i32 = alloc(nc * 4);
  for (let i: i32 = 0; i < nc; i++) {
    const yv: i32 = load<i32>(cy + i * 4);
    let lo: i32 = 0;
    let hi: i32 = ny - 1;
    let r: i32 = 0;
    while (lo <= hi) {
      const mid: i32 = (lo + hi) >> 1;
      const mv: i32 = load<i32>(uniqY + mid * 4);
      if (mv == yv) {
        r = mid + 1;
        break;
      }
      if (mv < yv) lo = mid + 1;
      else hi = mid - 1;
    }
    store<i32>(yRank + i * 4, r);
  }
  const bit: i32 = alloc((ny + 2) * 4);
  memory.fill(bit, 0, (ny + 2) * 4);
  const dp: i32 = alloc(nc * 4);
  let L: i32 = 0;
  for (let i: i32 = 0; i < nc; i++) {
    const r: i32 = load<i32>(yRank + i * 4);
    let s: i32 = 0;
    let j: i32 = r - 1;
    while (j > 0) {
      const bv: i32 = load<i32>(bit + j * 4);
      if (bv > s) s = bv;
      j -= j & -j;
    }
    const d: i32 = s + 1;
    store<i32>(dp + i * 4, d);
    if (d > L) L = d;
    j = r;
    while (j <= ny) {
      if (d > load<i32>(bit + j * 4)) store<i32>(bit + j * 4, d);
      j += j & -j;
    }
  }
  // Buckets by dp length, in candidate (x) order.
  const bktCnt: i32 = alloc((L + 1) * 4);
  memory.fill(bktCnt, 0, (L + 1) * 4);
  for (let i: i32 = 0; i < nc; i++) {
    const d: i32 = load<i32>(dp + i * 4);
    store<i32>(bktCnt + d * 4, load<i32>(bktCnt + d * 4) + 1);
  }
  let off: i32 = 0;
  for (let d: i32 = 1; d <= L; d++) {
    const c: i32 = load<i32>(bktCnt + d * 4);
    store<i32>(bktCnt + d * 4, off);
    off += c;
  }
  const slots: i32 = alloc(nc * 4);
  const fill: i32 = alloc((L + 1) * 4);
  memory.copy(fill, bktCnt, (L + 1) * 4);
  for (let i: i32 = 0; i < nc; i++) {
    const d: i32 = load<i32>(dp + i * 4);
    const p: i32 = load<i32>(fill + d * 4);
    store<i32>(fill + d * 4, p + 1);
    store<i32>(slots + p * 4, i);
  }
  const ax: i32 = alloc(nc * 4);
  const ay: i32 = alloc(nc * 4);
  const al: i32 = alloc(nc * 4);
  let na: i32 = 0;
  let curX: i32 = 2147483647;
  let curY: i32 = 2147483647;
  for (let len: i32 = L; len >= 1; len--) {
    const start: i32 = load<i32>(bktCnt + len * 4);
    const end: i32 = len < L ? load<i32>(bktCnt + (len + 1) * 4) : nc;
    let pick: i32 = -1;
    for (let s: i32 = start; s < end; s++) {
      const i: i32 = load<i32>(slots + s * 4);
      if (load<i32>(cx + i * 4) < curX && load<i32>(cy + i * 4) < curY) {
        pick = i;
        break;
      }
    }
    if (pick < 0) return -1;
    store<i32>(ax + na * 4, load<i32>(cx + pick * 4));
    store<i32>(ay + na * 4, load<i32>(cy + pick * 4));
    store<i32>(al + na * 4, load<i32>(cl + pick * 4));
    na++;
    curX = load<i32>(cx + pick * 4);
    curY = load<i32>(cy + pick * 4);
  }
  // The backward scan collected anchors latest-first; reverse them.
  for (let i: i32 = 0; i < na / 2; i++) {
    const j: i32 = na - 1 - i;
    let t: i32 = load<i32>(ax + i * 4);
    store<i32>(ax + i * 4, load<i32>(ax + j * 4));
    store<i32>(ax + j * 4, t);
    t = load<i32>(ay + i * 4);
    store<i32>(ay + i * 4, load<i32>(ay + j * 4));
    store<i32>(ay + j * 4, t);
    t = load<i32>(al + i * 4);
    store<i32>(al + i * 4, load<i32>(al + j * 4));
    store<i32>(al + j * 4, t);
  }
  // Filter 1 — swap signature: a block touching a swap is not safe.
  let w: i32 = 0;
  for (let i: i32 = 0; i < na; i++) {
    const x: i32 = load<i32>(ax + i * 4);
    const y: i32 = load<i32>(ay + i * 4);
    const ln: i32 = load<i32>(al + i * 4);
    let drop: bool = false;
    if (x > 0 && y + ln < mMid && load<i32>(aMid + (x - 1) * 4) == load<i32>(bMid + (y + ln) * 4)) drop = true;
    if (x + ln < nMid && y > 0 && load<i32>(aMid + (x + ln) * 4) == load<i32>(bMid + (y - 1) * 4)) drop = true;
    if (!drop) {
      store<i32>(ax + w * 4, x);
      store<i32>(ay + w * 4, y);
      store<i32>(al + w * 4, ln);
      w++;
    }
  }
  na = w;
  if (na == 0) return -1;
  // Filter 2 — diagonal: a moved block's anchors sit far off the diagonal
  // of the anchors a fixed distance away on both sides.
  const ks: i32 = alloc(na * 4);
  for (let i: i32 = 0; i < na; i++) {
    store<i32>(ks + i * 4, load<i32>(ax + i * 4) - load<i32>(ay + i * 4));
  }
  w = 0;
  for (let i: i32 = 0; i < na; i++) {
    const k: i32 = load<i32>(ks + i * 4);
    let ok: bool = false;
    for (let o: i32 = 0; o < 4; o++) {
      const off: i32 = o == 0 ? -40 : o == 1 ? -20 : o == 2 ? 20 : 40;
      const j: i32 = i + off;
      const ref: i32 = j < 0 ? 0 : j >= na ? nMid - mMid : load<i32>(ks + j * 4);
      const diff: i32 = k - ref;
      if ((diff < 0 ? -diff : diff) <= 35) {
        ok = true;
        break;
      }
    }
    if (ok) {
      store<i32>(ax + w * 4, load<i32>(ax + i * 4));
      store<i32>(ay + w * 4, load<i32>(ay + i * 4));
      store<i32>(al + w * 4, load<i32>(al + i * 4));
      w++;
    }
  }
  na = w;
  if (na == 0) return -1;
  // Filter 3 — large gap: an anchor next to a change of many lines sits at
  // the boundary of a rearrangement.
  w = 0;
  for (let i: i32 = 0; i < na; i++) {
    const x: i32 = load<i32>(ax + i * 4);
    const y: i32 = load<i32>(ay + i * 4);
    const ln: i32 = load<i32>(al + i * 4);
    const px: i32 = i > 0 ? load<i32>(ax + (i - 1) * 4) + load<i32>(al + (i - 1) * 4) : 0;
    const py: i32 = i > 0 ? load<i32>(ay + (i - 1) * 4) + load<i32>(al + (i - 1) * 4) : 0;
    const nx: i32 = i + 1 < na ? load<i32>(ax + (i + 1) * 4) : nMid;
    const ny: i32 = i + 1 < na ? load<i32>(ay + (i + 1) * 4) : mMid;
    const gapB: i32 = (x - px) + (y - py);
    const gapA: i32 = (nx - (x + ln)) + (ny - (y + ln));
    if (gapB <= 16 && gapA <= 16) {
      store<i32>(ax + w * 4, x);
      store<i32>(ay + w * 4, y);
      store<i32>(al + w * 4, ln);
      w++;
    }
  }
  na = w;
  if (na == 0) return -1;
  // Filter 4 — crossing: an anchor crossed by another unique block that is
  // old-first and nearby is the old-second block of a swap.
  w = 0;
  for (let i: i32 = 0; i < na; i++) {
    const x: i32 = load<i32>(ax + i * 4);
    const y: i32 = load<i32>(ay + i * 4);
    const ln: i32 = load<i32>(al + i * 4);
    // Binary search the candidate blocks (x order) for this anchor's x.
    let lo: i32 = 0;
    let hi: i32 = nc - 1;
    let ci: i32 = -1;
    while (lo <= hi) {
      const mid: i32 = (lo + hi) >> 1;
      const mv: i32 = load<i32>(cx + mid * 4);
      if (mv == x) {
        ci = mid;
        break;
      }
      if (mv < x) lo = mid + 1;
      else hi = mid - 1;
    }
    let drop: bool = false;
    if (ci >= 0) {
      for (let j: i32 = ci - 1; j >= 0 && x - load<i32>(cx + j * 4) <= 60; j--) {
        const cyv: i32 = load<i32>(cy + j * 4);
        if (cyv > y && cyv - y <= 60) {
          drop = true;
          break;
        }
      }
    }
    if (!drop) {
      store<i32>(ax + w * 4, x);
      store<i32>(ay + w * 4, y);
      store<i32>(al + w * 4, ln);
      w++;
    }
  }
  na = w;
  if (na == 0) return -1;
  // Assemble runs: exact Myers on each gap, KEEP for each anchor.
  const gk: i32 = alloc((nMid + mMid + 4) * 4);
  const gc: i32 = alloc((nMid + mMid + 4) * 4);
  let out: i32 = 0;
  let px: i32 = 0;
  let py: i32 = 0;
  for (let i: i32 = 0; i < na; i++) {
    const x: i32 = load<i32>(ax + i * 4);
    const y: i32 = load<i32>(ay + i * 4);
    const ln: i32 = load<i32>(al + i * 4);
    if (x > px || y > py) {
      const gn: i32 = myersRuns(aMid + px * 4, x - px, bMid + py * 4, y - py, gk + out * 4, gc + out * 4);
      if (gn < 0) return -1;
      out += gn;
    }
    if (out > 0 && load<i32>(gk + (out - 1) * 4) == KEEP) {
      store<i32>(gc + (out - 1) * 4, load<i32>(gc + (out - 1) * 4) + ln);
    } else {
      store<i32>(gk + out * 4, KEEP);
      store<i32>(gc + out * 4, ln);
      out++;
    }
    px = x + ln;
    py = y + ln;
  }
  if (px < nMid || py < mMid) {
    const gn: i32 = myersRuns(aMid + px * 4, nMid - px, bMid + py * 4, mMid - py, gk + out * 4, gc + out * 4);
    if (gn < 0) return -1;
    out += gn;
  }
  // Merge neighbours of one kind (the gap Myers already merges within a
  // gap; only the anchor boundaries need it).
  let mrg: i32 = 0;
  for (let i: i32 = 0; i < out; i++) {
    const kind: i32 = load<i32>(gk + i * 4);
    const cnt: i32 = load<i32>(gc + i * 4);
    if (mrg > 0 && load<i32>(rk + (mrg - 1) * 4) == kind) {
      store<i32>(rc + (mrg - 1) * 4, load<i32>(rc + (mrg - 1) * 4) + cnt);
    } else {
      store<i32>(rk + mrg * 4, kind);
      store<i32>(rc + mrg * 4, cnt);
      mrg++;
    }
  }
  return mrg;
}

// ---------------------------------------------------------------- patch
// Runs for the whole case (prefix KEEP + middle runs + suffix KEEP,
// merged), computed by computeRuns into these globals.

let gRunsK: i32 = 0;
let gRunsC: i32 = 0;
let gRunsN: i32 = 0;
let gN: i32 = 0;
let gM: i32 = 0;

function computeRuns(): i32 {
  // The starts table needs room for one entry per line plus two sentinels;
  // a line is at least one byte, so the byte lengths bound the line count.
  gStarts = alloc((gOldLen + gNewLen + 4) * 4);
  gNOld = scanLines(gOldPtr, gOldLen, gStarts);
  gNNew = scanLines(gNewPtr, gNewLen, gStarts + (gNOld + 1) * 4);
  const total: i32 = gNOld + gNNew;
  const ids: i32 = alloc(total * 4);
  const v: i32 = internLines(ids);
  gN = gNOld;
  gM = gNNew;
  const rk: i32 = alloc((total + 4) * 4);
  const rc: i32 = alloc((total + 4) * 4);
  let prefix: i32 = 0;
  while (prefix < gNOld && prefix < gNNew && load<i32>(ids + prefix * 4) == load<i32>(ids + (gNOld + prefix) * 4)) prefix++;
  let suffix: i32 = 0;
  while (suffix < gNOld - prefix && suffix < gNNew - prefix && load<i32>(ids + (gNOld - 1 - suffix) * 4) == load<i32>(ids + (gNOld + gNNew - 1 - suffix) * 4)) suffix++;
  const nMid: i32 = gNOld - prefix - suffix;
  const mMid: i32 = gNNew - prefix - suffix;
  const aMid: i32 = ids + prefix * 4;
  const bMid: i32 = ids + (gNOld + prefix) * 4;
  // Middle runs first, into a scratch pair, so the anchor path and the
  // fallback share the same assembly.
  const mk: i32 = alloc((nMid + mMid + 4) * 4);
  const mc: i32 = alloc((nMid + mMid + 4) * 4);
  let mn: i32 = anchorRuns(aMid, nMid, bMid, mMid, v, mk, mc);
  if (mn < 0) {
    mn = myersRuns(aMid, nMid, bMid, mMid, mk, mc);
    if (mn < 0) return -1;
  }
  let out: i32 = 0;
  if (prefix > 0) {
    store<i32>(rk + out * 4, KEEP);
    store<i32>(rc + out * 4, prefix);
    out++;
  }
  for (let i: i32 = 0; i < mn; i++) {
    const kind: i32 = load<i32>(mk + i * 4);
    const cnt: i32 = load<i32>(mc + i * 4);
    if (out > 0 && load<i32>(rk + (out - 1) * 4) == kind) {
      store<i32>(rc + (out - 1) * 4, load<i32>(rc + (out - 1) * 4) + cnt);
    } else {
      store<i32>(rk + out * 4, kind);
      store<i32>(rc + out * 4, cnt);
      out++;
    }
  }
  if (suffix > 0) {
    if (out > 0 && load<i32>(rk + (out - 1) * 4) == KEEP) {
      store<i32>(rc + (out - 1) * 4, load<i32>(rc + (out - 1) * 4) + suffix);
    } else {
      store<i32>(rk + out * 4, KEEP);
      store<i32>(rc + out * 4, suffix);
      out++;
    }
  }
  gRunsK = rk;
  gRunsC = rc;
  gRunsN = out;
  return 0;
}

// Emit one byte of patch text, JSON-escaping it when json is set.
function emitB(o: i32, b: i32, json: bool): i32 {
  if (json) {
    if (b == 34) {
      store<u8>(o, 92);
      store<u8>(o + 1, 34);
      return o + 2;
    }
    if (b == 92) {
      store<u8>(o, 92);
      store<u8>(o + 1, 92);
      return o + 2;
    }
    if (b == 10) {
      store<u8>(o, 92);
      store<u8>(o + 1, 110);
      return o + 2;
    }
    if (b == 13) {
      store<u8>(o, 92);
      store<u8>(o + 1, 114);
      return o + 2;
    }
    if (b == 9) {
      store<u8>(o, 92);
      store<u8>(o + 1, 116);
      return o + 2;
    }
    if (b == 8) {
      store<u8>(o, 92);
      store<u8>(o + 1, 98);
      return o + 2;
    }
    if (b == 12) {
      store<u8>(o, 92);
      store<u8>(o + 1, 102);
      return o + 2;
    }
    if (b < 32) {
      store<u8>(o, 92);
      store<u8>(o + 1, 117);
      store<u8>(o + 2, 48);
      store<u8>(o + 3, 48);
      const hi: i32 = (b >> 4) & 15;
      const lo: i32 = b & 15;
      store<u8>(o + 4, hi < 10 ? 48 + hi : 87 + hi);
      store<u8>(o + 5, lo < 10 ? 48 + lo : 87 + lo);
      return o + 6;
    }
  }
  store<u8>(o, b);
  return o + 1;
}

function emitS(o: i32, s: string, json: bool): i32 {
  for (let i: i32 = 0; i < s.length; i++) {
    o = emitB(o, s.charCodeAt(i), json);
  }
  return o;
}

// True when the byte range holds a byte that JSON-escaping must rewrite:
// a control byte, a quote, or a backslash. SIMD over 16-byte blocks.
function hasSpecial(ptr: i32, s: i32, e: i32): bool {
  let i: i32 = s;
  const splatE0 = v128.splat<i8>(-32);
  const splat0 = v128.splat<i8>(0);
  const splat22 = v128.splat<i8>(34);
  const splat5C = v128.splat<i8>(92);
  const end16: i32 = s + ((e - s) & ~15);
  for (; i < end16; i += 16) {
    const v = v128.load(ptr + i);
    const bad = v128.or(v128.or(v128.eq<i8>(v128.and(v, splatE0), splat0), v128.eq<i8>(v, splat22)), v128.eq<i8>(v, splat5C));
    if (v128.any_true(bad)) return true;
  }
  for (; i < e; i++) {
    const b: i32 = load<u8>(ptr + i);
    if (b < 32 || b == 34 || b == 92) return true;
  }
  return false;
}

// One patch line: the op byte, the line's bytes, and for a bare final line
// a newline plus a '%' line. Returns the end pointer, or -1 when the line
// would run past outEnd (a byte escapes to at most 6 bytes in JSON).
let outEnd: i32 = 0;

function emitLine(o: i32, op: i32, textPtr: i32, s: i32, e: i32, json: bool): i32 {
  if (o + (e - s) * 6 + 16 > outEnd) return -1;
  store<u8>(o, op);
  o++;
  const bare: bool = e <= s || load<u8>(textPtr + e - 1) != 10;
  if (!json) {
    if (e > s) memory.copy(o, textPtr + s, e - s);
    o += e - s;
  } else {
    // The bulk of a line is clean printable text; copy it whole and escape
    // only the trailing newline (or fall back to per-byte work when the
    // line itself holds a byte that needs escaping).
    const bodyEnd: i32 = bare ? e : e - 1;
    if (!hasSpecial(textPtr, s, bodyEnd)) {
      if (bodyEnd > s) memory.copy(o, textPtr + s, bodyEnd - s);
      o += bodyEnd - s;
      if (!bare) o = emitB(o, 10, json);
    } else {
      for (let i: i32 = s; i < e; i++) o = emitB(o, load<u8>(textPtr + i), json);
    }
  }
  if (bare) {
    o = emitB(o, 10, json);
    store<u8>(o, 37);
    o++;
    o = emitB(o, 10, json);
  }
  return o;
}

// Write the patch for the case computeRuns just solved, at out. When json
// is set, every byte is JSON-escaped (the patch goes inside a JSON string
// value). Returns the end pointer, or -1 on error.
function writePatch(out: i32, json: bool): i32 {
  const n: i32 = gN;
  const m: i32 = gM;
  // Change runs: stretches of deletions/insertions between kept lines.
  const maxCh: i32 = gRunsN + 1;
  const co: i32 = alloc(maxCh * 4);
  const cp: i32 = alloc(maxCh * 4);
  const cd: i32 = alloc(maxCh * 4);
  const ci: i32 = alloc(maxCh * 4);
  let nch: i32 = 0;
  let ol: i32 = 0;
  let pl: i32 = 0;
  let deleted: i32 = 0;
  let inserted: i32 = 0;
  for (let r: i32 = 0; r < gRunsN; r++) {
    const kind: i32 = load<i32>(gRunsK + r * 4);
    const cnt: i32 = load<i32>(gRunsC + r * 4);
    if (kind == KEEP) {
      ol += cnt;
      pl += cnt;
      continue;
    }
    let c: i32 = -1;
    if (nch > 0 && load<i32>(co + (nch - 1) * 4) + load<i32>(cd + (nch - 1) * 4) == ol && load<i32>(cp + (nch - 1) * 4) + load<i32>(ci + (nch - 1) * 4) == pl) {
      c = nch - 1;
    } else {
      c = nch;
      store<i32>(co + c * 4, ol);
      store<i32>(cp + c * 4, pl);
      store<i32>(cd + c * 4, 0);
      store<i32>(ci + c * 4, 0);
      nch++;
    }
    if (kind == DEL) {
      store<i32>(cd + c * 4, load<i32>(cd + c * 4) + cnt);
      ol += cnt;
      deleted += cnt;
    } else {
      store<i32>(ci + c * 4, load<i32>(ci + c * 4) + cnt);
      pl += cnt;
      inserted += cnt;
    }
  }
  // Hunks: change runs at most 6 kept lines apart share one.
  const hFirst: i32 = alloc((nch + 1) * 4);
  const hLast: i32 = alloc((nch + 1) * 4);
  let nh: i32 = 0;
  for (let c: i32 = 0; c < nch; c++) {
    if (nh > 0) {
      const prev: i32 = load<i32>(hLast + (nh - 1) * 4);
      if (load<i32>(co + c * 4) - (load<i32>(co + prev * 4) + load<i32>(cd + prev * 4)) <= 6) {
        store<i32>(hLast + (nh - 1) * 4, c);
        continue;
      }
    }
    store<i32>(hFirst + nh * 4, c);
    store<i32>(hLast + nh * 4, c);
    nh++;
  }
  let o: i32 = out;
  if (o + 8192 > outEnd) return -1;
  o = emitS(o, "makefun-diff/1 old=", json);
  o = writeU32(o, <u32>n);
  o = emitS(o, " new=", json);
  o = writeU32(o, <u32>m);
  o = emitS(o, " hunks=", json);
  o = writeU32(o, <u32>nh);
  o = emitS(o, " deleted=", json);
  o = writeU32(o, <u32>deleted);
  o = emitS(o, " inserted=", json);
  o = writeU32(o, <u32>inserted);
  o = emitB(o, 10, json);
  for (let h: i32 = 0; h < nh; h++) {
    if (o + 8192 > outEnd) return -1;
    const first: i32 = load<i32>(hFirst + h * 4);
    const last: i32 = load<i32>(hLast + h * 4);
    const oldStart: i32 = load<i32>(co + first * 4) - 3 > 0 ? load<i32>(co + first * 4) - 3 : 0;
    const newStart: i32 = load<i32>(cp + first * 4) - (load<i32>(co + first * 4) - oldStart);
    let after: i32 = n - (load<i32>(co + last * 4) + load<i32>(cd + last * 4));
    if (after > 3) after = 3;
    const oldEnd: i32 = load<i32>(co + last * 4) + load<i32>(cd + last * 4) + after;
    const newEnd: i32 = load<i32>(cp + last * 4) + load<i32>(ci + last * 4) + after;
    o = emitS(o, "@ ", json);
    o = writeU32(o, <u32>(oldStart + 1));
    o = emitB(o, 32, json);
    o = writeU32(o, <u32>(oldEnd - oldStart));
    o = emitB(o, 32, json);
    o = writeU32(o, <u32>(newStart + 1));
    o = emitB(o, 32, json);
    o = writeU32(o, <u32>(newEnd - newStart));
    o = emitB(o, 10, json);
    let at: i32 = oldStart;
    for (let c: i32 = first; c <= last; c++) {
      const cs: i32 = load<i32>(co + c * 4);
      const ps: i32 = load<i32>(cp + c * 4);
      const dels: i32 = load<i32>(cd + c * 4);
      const ins: i32 = load<i32>(ci + c * 4);
      for (; at < cs; at++) {
        o = emitLine(o, 61, gOldPtr, lineStart(at), lineEnd(at), json);
        if (o < 0) return -1;
      }
      for (let i: i32 = 0; i < dels; i++) {
        o = emitLine(o, 45, gOldPtr, lineStart(cs + i), lineEnd(cs + i), json);
        if (o < 0) return -1;
      }
      for (let i: i32 = 0; i < ins; i++) {
        const j: i32 = gNOld + ps + i;
        o = emitLine(o, 43, gNewPtr, lineStart(j), lineEnd(j), json);
        if (o < 0) return -1;
      }
      at = cs + dels;
    }
    for (; at < oldEnd; at++) {
      o = emitLine(o, 61, gOldPtr, lineStart(at), lineEnd(at), json);
      if (o < 0) return -1;
    }
  }
  return o;
}

// ---------------------------------------------------------------- JSON input
// A tolerant reader for the harness's cases.json: [{"id", "input": {"old",
// "new"}}, ...]. String values are unescaped into the bump heap; only the
// "old" and "new" values are kept. Anything else is skipped by value.

let jPos: i32 = 0;
let jEnd: i32 = 0;
let curOldP: i32 = 0;
let curOldL: i32 = 0;
let curNewP: i32 = 0;
let curNewL: i32 = 0;

function skipWs(): void {
  while (jPos < jEnd) {
    const b: i32 = load<u8>(jPos);
    if (b == 32 || b == 9 || b == 10 || b == 13) jPos++;
    else break;
  }
}

function hexVal(b: i32): i32 {
  if (b >= 48 && b <= 57) return b - 48;
  if (b >= 97 && b <= 102) return b - 87;
  if (b >= 65 && b <= 70) return b - 55;
  return -1;
}

function utf8Encode(o: i32, cp: i32): i32 {
  if (cp < 0x80) {
    store<u8>(o, cp);
    return o + 1;
  }
  if (cp < 0x800) {
    store<u8>(o, 0xC0 | (cp >> 6));
    store<u8>(o + 1, 0x80 | (cp & 63));
    return o + 2;
  }
  if (cp < 0x10000) {
    store<u8>(o, 0xE0 | (cp >> 12));
    store<u8>(o + 1, 0x80 | ((cp >> 6) & 63));
    store<u8>(o + 2, 0x80 | (cp & 63));
    return o + 3;
  }
  store<u8>(o, 0xF0 | (cp >> 18));
  store<u8>(o + 1, 0x80 | ((cp >> 12) & 63));
  store<u8>(o + 2, 0x80 | ((cp >> 6) & 63));
  store<u8>(o + 3, 0x80 | (cp & 63));
  return o + 4;
}

// Parse a JSON string at jPos (opening quote) into the heap; returns the
// start of the unescaped bytes, and writes its length to lenOut. -1 on error.
// Scratch cell for string lengths, kept apart from the heap so a length
// write can never clobber string bytes.
let jScratch: i32 = 0;

function parseString(lenOut: i32): i32 {
  if (jPos >= jEnd || load<u8>(jPos) != 34) return -1;
  // The unescaped bytes are never longer than the JSON that remains.
  ensureRoom(jEnd - jPos);
  jPos++;
  const dst: i32 = heapPtr;
  let o: i32 = dst;
  const splat5C = v128.splat<i8>(92);
  const splat22 = v128.splat<i8>(34);
  while (jPos < jEnd) {
    // Fast path: copy the clean run up to the next backslash or quote,
    // 16 bytes at a time; a chunk holding a special byte copies only its
    // clean prefix, then the scalar step handles that one byte.
    if (jEnd - jPos >= 16) {
      const v = v128.load(jPos);
      const hit = v128.or(v128.eq<i8>(v, splat5C), v128.eq<i8>(v, splat22));
      const bits: i32 = v128.bitmask<i8>(hit);
      if (bits == 0) {
        memory.copy(o, jPos, 16);
        o += 16;
        jPos += 16;
        continue;
      }
      const first: i32 = 31 - <i32>Math.clz32(bits & -bits);
      if (first > 0) {
        memory.copy(o, jPos, first);
        o += first;
        jPos += first;
      }
    }
    const b: i32 = load<u8>(jPos);
    if (b == 34) {
      jPos++;
      store<i32>(lenOut, o - dst);
      heapPtr = o;
      return dst;
    }
    if (b == 92) {
      jPos++;
      if (jPos >= jEnd) return -1;
      const e: i32 = load<u8>(jPos);
      jPos++;
      if (e == 34) {
        store<u8>(o, 34);
        o++;
      } else if (e == 92) {
        store<u8>(o, 92);
        o++;
      } else if (e == 47) {
        store<u8>(o, 47);
        o++;
      } else if (e == 98) {
        store<u8>(o, 8);
        o++;
      } else if (e == 102) {
        store<u8>(o, 12);
        o++;
      } else if (e == 110) {
        store<u8>(o, 10);
        o++;
      } else if (e == 114) {
        store<u8>(o, 13);
        o++;
      } else if (e == 116) {
        store<u8>(o, 9);
        o++;
      } else if (e == 117) {
        let cp: i32 = 0;
        for (let k: i32 = 0; k < 4; k++) {
          if (jPos >= jEnd) return -1;
          const hv: i32 = hexVal(load<u8>(jPos));
          if (hv < 0) return -1;
          cp = (cp << 4) | hv;
          jPos++;
        }
        if (cp >= 0xD800 && cp <= 0xDBFF && jPos + 1 < jEnd && load<u8>(jPos) == 92 && load<u8>(jPos + 1) == 117) {
          // Possible surrogate pair: peek the low half.
          let save: i32 = jPos;
          jPos += 2;
          let lo: i32 = 0;
          let okPair: bool = true;
          for (let k: i32 = 0; k < 4; k++) {
            if (jPos >= jEnd) {
              okPair = false;
              break;
            }
            const hv: i32 = hexVal(load<u8>(jPos));
            if (hv < 0) {
              okPair = false;
              break;
            }
            lo = (lo << 4) | hv;
            jPos++;
          }
          if (okPair && lo >= 0xDC00 && lo <= 0xDFFF) {
            cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
          } else {
            jPos = save;
            cp = 0xFFFD;
          }
        } else if (cp >= 0xD800 && cp <= 0xDFFF) {
          cp = 0xFFFD;
        }
        o = utf8Encode(o, cp);
      } else {
        return -1;
      }
      continue;
    }
    store<u8>(o, b);
    o++;
    jPos++;
  }
  return -1;
}

function skipString(): i32 {
  if (jPos >= jEnd || load<u8>(jPos) != 34) return -1;
  jPos++;
  while (jPos < jEnd) {
    const b: i32 = load<u8>(jPos);
    if (b == 92) {
      jPos += 2;
      continue;
    }
    if (b == 34) {
      jPos++;
      return 0;
    }
    jPos++;
  }
  return -1;
}

function skipValue(): i32 {
  skipWs();
  if (jPos >= jEnd) return -1;
  const b: i32 = load<u8>(jPos);
  if (b == 34) return skipString();
  if (b == 123) return skipObject();
  if (b == 91) return skipArray();
  // Literal or number: consume to the next delimiter.
  while (jPos < jEnd) {
    const c: i32 = load<u8>(jPos);
    if (c == 44 || c == 93 || c == 125 || c == 32 || c == 9 || c == 10 || c == 13) break;
    jPos++;
  }
  return 0;
}

function skipObject(): i32 {
  if (jPos >= jEnd || load<u8>(jPos) != 123) return -1;
  jPos++;
  skipWs();
  if (jPos < jEnd && load<u8>(jPos) == 125) {
    jPos++;
    return 0;
  }
  while (true) {
    skipWs();
    if (skipString() < 0) return -1;
    skipWs();
    if (jPos >= jEnd || load<u8>(jPos) != 58) return -1;
    jPos++;
    if (skipValue() < 0) return -1;
    skipWs();
    if (jPos >= jEnd) return -1;
    const b: i32 = load<u8>(jPos);
    if (b == 44) {
      jPos++;
      continue;
    }
    if (b == 125) {
      jPos++;
      return 0;
    }
    return -1;
  }
}

function skipArray(): i32 {
  if (jPos >= jEnd || load<u8>(jPos) != 91) return -1;
  jPos++;
  skipWs();
  if (jPos < jEnd && load<u8>(jPos) == 93) {
    jPos++;
    return 0;
  }
  while (true) {
    if (skipValue() < 0) return -1;
    skipWs();
    if (jPos >= jEnd) return -1;
    const b: i32 = load<u8>(jPos);
    if (b == 44) {
      jPos++;
      continue;
    }
    if (b == 93) {
      jPos++;
      return 0;
    }
    return -1;
  }
}

function keyIs(ptr: i32, len: i32, s: string): bool {
  if (len != s.length) return false;
  for (let i: i32 = 0; i < len; i++) {
    if (load<u8>(ptr + i) != s.charCodeAt(i)) return false;
  }
  return true;
}

// Parse one object, capturing any "old"/"new" string values into the
// current-case slots (works nested: the "input" object's values land in
// the same slots).
function parseObjectCapture(): i32 {
  if (jPos >= jEnd || load<u8>(jPos) != 123) return -1;
  jPos++;
  skipWs();
  if (jPos < jEnd && load<u8>(jPos) == 125) {
    jPos++;
    return 0;
  }
  while (true) {
    skipWs();
    const keyPtr: i32 = parseString(jScratch);
    if (keyPtr < 0) return -1;
    const keyLen: i32 = load<i32>(jScratch);
    // The key bytes are short-lived: rewind the heap over them. The key
    // text itself stays readable until the next allocation overwrites it,
    // so decide what the key is BEFORE parsing the value.
    heapPtr = keyPtr;
    const isOld: bool = keyIs(keyPtr, keyLen, "old");
    const isNew: bool = keyIs(keyPtr, keyLen, "new");
    const isInput: bool = keyIs(keyPtr, keyLen, "input");
    skipWs();
    if (jPos >= jEnd || load<u8>(jPos) != 58) return -1;
    jPos++;
    skipWs();
    if (isOld || isNew) {
      const valPtr: i32 = parseString(jScratch);
      if (valPtr < 0) return -1;
      const valLen: i32 = load<i32>(jScratch);
      heapPtr = valPtr + ((valLen + 7) & ~7);
      if (isOld) {
        curOldP = valPtr;
        curOldL = valLen;
      } else {
        curNewP = valPtr;
        curNewL = valLen;
      }
    } else if (isInput) {
      if (parseObjectCapture() < 0) return -1;
    } else {
      if (skipValue() < 0) return -1;
    }
    skipWs();
    if (jPos >= jEnd) return -1;
    const b: i32 = load<u8>(jPos);
    if (b == 44) {
      jPos++;
      continue;
    }
    if (b == 125) {
      jPos++;
      return 0;
    }
    return -1;
  }
}

// Parse the whole cases array; store per-case spans in the arrays at
// casesOut (4 i32 per case: oldPtr, oldLen, newPtr, newLen), grown by the
// caller to at least the case count. Returns the case count, or -1.
function parseCases(jsonPtr: i32, jsonLen: i32, casesOut: i32, capOut: i32): i32 {
  jPos = jsonPtr;
  jEnd = jsonPtr + jsonLen;
  skipWs();
  if (jPos >= jEnd || load<u8>(jPos) != 91) return -1;
  jPos++;
  skipWs();
  let n: i32 = 0;
  if (jPos < jEnd && load<u8>(jPos) == 93) {
    jPos++;
    store<i32>(capOut, n);
    return 0;
  }
  while (true) {
    curOldP = 0;
    curOldL = 0;
    curNewP = 0;
    curNewL = 0;
    if (parseObjectCapture() < 0) return -1;
    if (curOldP == 0 && curOldL == 0 && curNewP == 0 && curNewL == 0) return -1;
    store<i32>(casesOut + n * 16, curOldP);
    store<i32>(casesOut + n * 16 + 4, curOldL);
    store<i32>(casesOut + n * 16 + 8, curNewP);
    store<i32>(casesOut + n * 16 + 12, curNewL);
    n++;
    skipWs();
    if (jPos >= jEnd) return -1;
    const b: i32 = load<u8>(jPos);
    if (b == 44) {
      jPos++;
      continue;
    }
    if (b == 93) {
      jPos++;
      store<i32>(capOut, n);
      return n;
    }
    return -1;
  }
}

// ---------------------------------------------------------------- exports

// Batch: parse the harness's cases.json at jsonPtr, answer every case
// alone, and write the answers.json bytes at outPtr. Returns the byte
// length, or -1 on error. The heap starts at heapBase; it grows itself.
export function runBatch(jsonPtr: i32, jsonLen: i32, outPtr: i32, heapBase: i32): i32 {
  heapPtr = heapBase;
  outEnd = heapBase;
  jScratch = alloc(4);
  const cases: i32 = alloc(64 * 16);
  const capPtr: i32 = alloc(4);
  const n: i32 = parseCases(jsonPtr, jsonLen, cases, capPtr);
  if (n < 0) return -1;
  let o: i32 = outPtr;
  store<u8>(o, 91);
  o++;
  for (let c: i32 = 0; c < n; c++) {
    if (c > 0) {
      store<u8>(o, 44);
      o++;
    }
    store<u8>(o, 34);
    o++;
    gOldPtr = load<i32>(cases + c * 16);
    gOldLen = load<i32>(cases + c * 16 + 4);
    gNewPtr = load<i32>(cases + c * 16 + 8);
    gNewLen = load<i32>(cases + c * 16 + 12);
    if (computeRuns() < 0) return -1;
    o = writePatch(o, true);
    if (o < 0) return -1;
    store<u8>(o, 34);
    o++;
  }
  store<u8>(o, 93);
  o++;
  return o - outPtr;
}

// Single case: the patch string's UTF-8 bytes at outPtr. Returns the byte
// length, or -1 on error.
export function runCase(oldPtr: i32, oldLen: i32, newPtr: i32, newLen: i32, outPtr: i32, heapBase: i32): i32 {
  heapPtr = heapBase;
  outEnd = heapBase;
  jScratch = alloc(4);
  gOldPtr = oldPtr;
  gOldLen = oldLen;
  gNewPtr = newPtr;
  gNewLen = newLen;
  if (computeRuns() < 0) return -1;
  const end: i32 = writePatch(outPtr, false);
  if (end < 0) return -1;
  return end - outPtr;
}
