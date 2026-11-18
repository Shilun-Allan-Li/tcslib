Owner-side PR **O2** of GSW phase 6b (P6-Q7, r3 §H5.8): the decoding interval of `LWE/BitEncoding.lean`. It adds `decodeLo` and `decodeHi` with their `rfl` readers `decodeLo_eq` and `decodeHi_eq`, and `decode_iff_mem_Ico`, proved: `decode P v ↔ decodeLo P ≤ v.val < decodeHi P`. The 6b statement PR (#377) is stacked on this one.

## Scope and commit
- **Head:** `04ba2446f541c39dd02aefaa97a9eb31dbbda748`, a maintainer-signed cherry-pick (`-S`) of the worker's `5bd5ada5f42c5e1228ea84ad70f4d8c52a3644fd` (delivery `inbox/fills/gsw-6b-statements/` at exchange `3b340824dde77433b2135a3c8d20c7ed194cf18c`). The worker's message and trailers are kept.
- **Base:** the records tip `38123ccbebef878cd25dd2d2761de1b40ba7e421`, which is Lean-equal to olean snapshot #10's T `cf6a2266` (#366 and #368 merged; all 6a targets proved). The tree `8b615e06` equals `git merge-tree` of the tip and `5bd5ada5`.
- **Range-diff** against the delivered series: 1/1 `=`.
- **Files:** `TCSlib/Cryptography/LWE/BitEncoding.lean` only, insertions only (+58/−0): two module-docstring entries and the five declarations above. Each has a formula docstring and "Glue"; the theorem has a proof sketch, rewriting both distances with Mathlib's `ZMod.valMinAbs_natAbs_eq_min`.

## Rulings
- **P6-Q7:** O2 lands owner-side before the statements. It reproduces hash for hash on the issued base (phase 1).
- **Q-6B-W1, W2, W3** (accepted as delivered), **Q-6B-F1** (LE-6b1..3) and **Q-6B-F2** (`decDepth_le` stays admitted) apply to the statement PR. This PR has no landing edit.

## Checks (maintainer phase 2: this head replayed on olean snapshot #10; `briefs/lattice-gsw/phase6/final-6b-r1/phase2.md`, R1)
- **Build:** the tree was a `cp -al` copy of snapshot #10 with the Mathlib overlay. BitEncoding and its 18 downstream modules rebuilt, 1428 were reused. All 19 have rc 0, 0 `error:` and 0 `error(`, and 0 `sorry`. The 3 warnings are pre-existing and equal to the delivery's O2 sweep logs. The state check gives 1447/1447 OK, and the 19 rebuilt oleans have link count 1. Snapshot #10 rehashed 0/0/0 before, after and at the end.
- **Admissions:** 192 at the tip and 192 here (+0). The per-module census is identical.
- **decls2** (tip against the head): **5 ADDED** (`decodeLo`, `decodeHi`, `decodeLo_eq`, `decodeHi_eq`, `decode_iff_mem_Ico`), 0 CHANGED, 0 REMOVED.
- **Axioms:** all 24 BitEncoding constants are standard. `decodeLo`, `decodeHi` and their readers use none; `decode_iff_mem_Ico` uses `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx`.
- **Rule 10** on `BitEncoding`:
  - seals strict A/B and coe A/B: 9/9/9/9 requests, 0 errors, install and EOF records `requested = verified`;
  - the delivery's 5 paired controls on `decodeLo`, run unchanged: ALL_OK. The unsealed body read gives 0 errors. Sealed, strict and coe, the negative gives exactly 1 error, in the example, and the reader 0;
  - explicit-unfold scan: 54 items, 0 foreign.
- **Lint:** `campaign_style_lint TCSlib/Cryptography --check8b` FAIL/WARN lines are identical to the tip's (92/103). `style_lint` finds 0 problems.
- **Output map** (Mathlib excluded): 1478 entries, `e1d210bf…`. Against snapshot #10, only `LWE/BitEncoding` differs.

## Disclosed
- The inline step `hsub`, the two-case value of `v − ⌊q/2⌋`, has no `ZMod` lemma in Mathlib. Phase 1 checked this.
- The issued `o2check.py` gives 0 mismatches for 2 ≤ q ≤ 2000. The delivery's kernel `decide` probe covers q ≤ 63.

## Review and merge order
- **Verdict:** **ACCEPT** (`briefs/lattice-gsw/phase6/final-6b-r1/review.md`, phases 1 and 2). **Gate 46 (Codex) audits both** this PR and the stacked statement PR (#377).
- **Merge order:** this PR merges **first**. Then the statement PR, stacked on `land/gsw-6b-o2`, is retargeted to `cryptography/pass-shelat-ch2-4`.
- **Snapshot:** on merge, if the merge's Lean paths equal tree `8b615e06`, `olean-replay-6b-o2` can be adopted (map `e1d210bf…`).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA