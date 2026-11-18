# GSW 6b U13 `gsw-6b-u13` · final r1 · phase 2: replay on olean snapshot #11

**Verdict: PASS, with no new finding.** This is the same run as U12's phase 2: one replay tree with
U12 and U13 stacked (U12, then U13), then each unit **alone** on its own copy of the snapshot.
[`../../U12/final-r1/phase2.md`](../../U12/final-r1/phase2.md) gives the full recipe log: inputs,
heads, copy, overlay, plan, acceptance and lint. This file repeats the shared numbers and gives
U13's own. `GSW/DecryptFormula.lean` compiles at B6 + U13 and at B6 + U12 + U13, and its olean is
byte-identical in both.

- **Build.**
  - **Stack:** 12/12 modules rc 0, including the root `TCSlib`. There were 0 `error:`/`error(`, and
    `DecryptFormula`'s log is empty.
  - **U13 alone:** 11/11 rc 0, with admissions **36 in 15** = `base-sorries.txt` minus the six
    targets.
  - **Checks.** No `audits/*/Checks` imports a changed module. Both are in the full order, reused,
    and pass the state check.
- **Axioms.** All 23 stored constants are standard, with 0 `sorryAx`. The six targets are each
  `[propext, Classical.choice, Quot.sound]`.
- **Seals.** Canonical coe-A and seal B: rc 0 with 0 errors, 380 requested and 380 verified.
- **Controls.** 2 liveness pairs, ALL_OK.
- **Unfold scan.** 0 definitions.
- **Duplication probes.** No lemma found.
- **Lint.** Unchanged.
- **Snapshot #11.** Rehashes 0/0/0 before, after the build and at the end.

Run on 2026-11-18 from 22:28 to 22:42 UTC in
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g6b-u1213/`.

- **Lean processes.** One at a time: 46 starts plus `mathlibextra`. Every start was gated at ≤ 2
  other Lean processes and ≥ 2,000 MB free. There was never more than 1 other process, no wait, and
  the lowest free disk was 2,771 MB.
- **Not done.** No `lake build`, cache get, commit, branch, push or PR.
- The snapshot was read and hard-linked only.

## P2-1 Heads (scratch only)

- **Reproduction.** The patch on B6 gives `74fb355a17a47076d7de44a0f691ea03572cb170`
  (`logs/repro-u13.log`).
- **Stack check head.** `51d46089e37030f582b24c1f84ee68ac21c98829`, tree `fb6884d1…`, which equals
  `git merge-tree --write-tree afdaa9e2 74fb355a`.
- **The records tip.** `31247fe7…` is Lean-equal to B6. The merge-tree of `74fb355a` with it is
  clean (`62e193f2…`).

## P2-2 Stack replay (shared with U12)

- **Copy.** `cp -al` of snapshot #11 (1,487 files), with 3,346 Mathlib symlinks. `NthRootLemmas` is
  `c0a9cff0…`.
- **Plan.** Changed 2, down 12, **12 to build and 1,444 to reuse**. The order is `Branching`,
  `DecryptFormula`, `Bootstrap`, `Circular`, `Leveled`, `LeveledSecurity`, `PolyRatio`,
  `Asymptotic`, `GSW`, `Homomorphic`, `AdvancedEncryption`, `TCSlib`.
- **Build.** 22:29:27–22:30:00, **12/12 rc 0**.
  - 0 errors in both forms, and the substring "error" occurs 0 times.
  - The 15 `sorry` warnings are the other units' targets. There are no other warnings.
  - `DecryptFormula` took 1.98 s.
- **Accept.**
  - `permod`: 0 bad.
  - `stateplan update`: 12 taken, with sources bound to `git show 51d46089:<path>`.
  - `check`: **1,456/1,456, RESULT OK**, again at the end.
  - Link count 1 for exactly the 12 plus `NthRootLemmas`.
  - Snapshot verify **0/0/0**.
- **Admissions at the stack:** **33 in 14**. The removed rows are G1–G3 and U13's six; nothing was
  added.

## P2-3 U13 alone

`alone.sh u13 74fb355a`:
- **Copy and plan.** A fresh `cp -al` copy with the same overlay. Changed 1, down 11, **11 to build
  and 1,445 to reuse**.
- **Build.** **11/11 rc 0**, 0/0 errors.
- **Accept.** `stateplan update` takes 11, and `check` gives **1,456 RESULT OK**. Link count 1 for
  the 11.
- **Admissions:** **36 in 15**. Only `vecMul_secretVector_eq_sum`, `decryptFormula_eval`,
  `nandFormula_eval`, `depth_nandFormula_le`, `maxFanin_nandFormula_le` and `decDepth_le` are
  removed, which is the brief's C2 count.
- **`DecryptFormula.olean` equals the stack's** (`8f73be82…`).
- The copy was deleted after its records were kept (`alone/u13/`).

## P2-4 Axioms

`G6bProbe/Axioms`: rc 0. `DecryptFormula` has **23 stored constants**, the same 23 as the worker's
census, with the same sets.

| Axiom set | Constants |
|---|---|
| `[Classical.choice, Quot.sound, propext]` | 20: the 16 declarations other than the instance, plus the 4 `_proof_` auxiliaries of `decDepth_le` (2), `depth_nandFormula_le` and `maxFanin_nandFormula_le` |
| `[Quot.sound, propext]` | 2: `decryptFormula_eval._proof_1_1`, `_1_2` |
| `[propext]` | 1: `Parameters.neZero_columns` |

- **0 non-standard, 0 `sorryAx`.**
- **Targets.** `#print axioms` of G5, G6, G7 and the three G8 declarations: each `[propext,
  Classical.choice, Quot.sound]`.
- **Control.** The `sorry` control is flagged `[sorryAx]`.

## P2-5 Rule 10

- **Collector.** `Collect`, rc 0, gives 606 CAT rows and `DecryptFormula: stored 23`.
- **Canonical coe-A** (`mkseals_coe.py`, A variant, unmodified):
  - **380 requests**: every ordinary TCSlib definition of the closure, including `decrypt`,
    `decode`, `decodeLo`/`decodeHi`, `decomposeVec`, `gadget`, `secretVector`, `decryptColumn`,
    `modSumInterval` and `modSumDepth`.
  - 21 term names, of which 15 are in the closure and 6 are excluded abbreviations: `Ciphertext`,
    `Parameters.columns`, `lwe`, `width`, and `LWE.Parameters.dimension`, `modulus`.
  - **Result: rc 0 and 0 errors in 39 s.** `G06-SEAL requested=380 active=363
    already_irreducible=17 verified=380`, and the end record has `verified=380`.
- **Seal B:** the same 380 requests, since `PolyExpr.eval` is not in the closure. It gives **rc 0
  and 0 errors**, with verified = requested.
- **The `FinDist` coercion.** It is excluded as notation in both variants, as the canonical tool
  does. The worker reports it in this closure (`coe-excluded=1`).
- **Liveness pairs** (appended to the canonical sealed copy and to the head source; `mkctl.py`):

  | Pair | Sealed | Open |
  |---|---|---|
  | `GSW.decrypt` / `decrypt_eq` (phase-5 `Scheme.lean`) | NEG line 447: 1 error (Type mismatch); POS 448 passes | 0 errors |
  | `LWE.BitEncoding.decodeLo` / `decodeLo_eq` (O2) | NEG line 451: 1 error; POS 452 passes | 0 errors |

  Sealed: exactly 2 errors, one at each NEG line, so the result is **ALL_OK**.
- **Explicit-unfold scan.** `DecryptFormula` has 35 identifiers passed to `rw`, and **0 TCSlib
  definitions** among them. All are theorems (the readers, O2, F1/F3/F9/F10 and Mathlib) or local
  hypotheses (`ht`, `hcast`, `hval`).

## P2-6 Duplication probes

`G6bProbe/DupProbe` runs `exact?` with 400k heartbeats:
- **D3:** the general Boolean-weighted `ZMod` sum representative, G6's `hval`.
- **D4:** `decodeLo P ≤ decodeHi P` and `decodeHi P ≤ P.modulus`, G6's `hlh`/`hhq`.

`exact?` finds **no lemma** for either. The run is rc 1 by design; D1/D2 are U12's.

## P2-7 Lint

- `campaign_style_lint --check8b`: **92 FAIL / 103 WARN over 540 files** at B6, at `74fb355a` and
  at the stack, with identical line sets. `DecryptFormula`'s only line is INFO (216 → 264).
- `style_lint`: 0 findings.

## P2-8 State after the run

- **Deleted:** all three replay trees, after the end-of-run state check. The scratch worktree was
  removed after zipping.
- **Snapshot #11:** 0/0/0 at 22:42Z.
- **Evidence:** `gsw-6b-u12-u13-final-r1-evidence.zip`, beside this file. It is the same zip as
  U12's.

## What this changes in `review.md`

| Item | Phase 1 | After phase 2 |
|---|---|---|
| C1/C2 | worker's sweep (root not built) | **reproduced**, with root `TCSlib`; U13 alone 36 in 15 |
| C5 | worker's census | **reproduced**: 23/23, same sets |
| C6 | worker's whole-closure seals | **canonical coe-A and B** pass at 380 requests; 2 liveness pairs; unfold scan 0 |
| Duplication | static | `exact?` probes D3/D4 find no lemma |
| New findings | none | none |
