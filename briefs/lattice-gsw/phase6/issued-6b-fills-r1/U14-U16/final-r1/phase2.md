# GSW 6b U14+U16 `gsw-6b-u14-u16` · final r1 · phase 2: replay on olean snapshot #11

**Verdict: PASS, with no new finding against the delivery.** Two replay trees were built, each a `cp -al` copy of
snapshot #11:

- **B6 run:** the unit head `9852429e` on B6, as the brief and the recipe require.
- **Stacked run:** the unit merged onto the records tip, which already carries U12 and U13 (#392). This is the tree the
  landing PR produces.

`GSW/Bootstrap.lean` and `GSW/Leveled.lean` compile in both, and both oleans are **byte-identical** between the two
runs.

- **Build.**
  - **B6:** 10/10 modules rc 0, including the root `TCSlib`. There were 0 `error:`/`error(`, the substring "error"
    occurs 0 times, and the only warnings are the 8 `sorry` warnings of other units' targets. Admissions are **35 in
    14**, which is `base-sorries.txt` minus the seven targets (the brief's C2 count).
  - **Stacked:** 12/12 modules rc 0, including the root `TCSlib`, with 0/0 errors and the same 8 warnings. Admissions
    are **26 in 12**, which is the base minus U12's 3, U13's 6 and this unit's 7.
  - **Checks.** No `audits/*/Checks` imports a changed module. Both are in the full order, reused, and pass the state
    check.
- **Axioms.** The census covers all 65 stored constants of the two modules.
  - **B6:** no axiom other than `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. 8 constants reach `sorryAx`:
    the seven targets and `encrypts_bootGate`. Every trace names only allowed U12/U13 targets (0 disallowed, 0 owner
    declarations).
  - **Stacked:** 0 `sorryAx`. All eight are `[propext, Classical.choice, Quot.sound]`.
- **Seals.** Canonical coe-A and seal B give rc 0 and 0 errors on both owners, on both heads. Bootstrap verified 444
  of 444 requests, and Leveled 479 of 479.
- **Controls.** 6 liveness pairs (2 for Bootstrap, 4 for Leveled, two of them for `encrypts_bootGate`), ALL_OK.
- **Unfold scan.** 0 foreign definitions.
- **Duplication probes.** D1–D7, each with its use's hypotheses, find no lemma. D5's only hit is `exact rfl`, a defeq
  read of the foreign `LWE.sample`.
- **Lint.** Unchanged at B6, at the head, at the records tip and at the stack.
- **Snapshot #11.** Rehashes 0/0/0 before, after the build, at the end, and after the trees were deleted.

Run on 2026-11-19 from 01:16 to 01:36 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`. The work directory is
`$SP/g6b-u1416/`.

- **Lean processes.** One at a time: 41 starts, `mathlibextra` included.
  - Each start went through `runq.sh` (the U12/U13 review's copy), which checks before the start that at most 2 other
    Lean processes are running (`pgrep -fc "bin/lean "`) and at least 2,000 MB is free. Each start is logged in
    `logs/slot.log`.
  - Two other jobs ran Lean throughout. At 35 starts there was 1 other process on the host and at 6 there were 2, so
    the machine never had more than 3. No start waited.
  - The lowest free disk at a start was **6,682 MB**.
- **Not done.** No `lake build`, no cache get, no commit, no branch, no push, no PR.
- **Not touched.** The snapshot was read and hard-linked only. No existing `$SP/olean-replay-*` tree was touched, and no
  other job's process.
- **Deleted at the end:** my two replay trees and the scratch worktree. Each tree rebuilds in about a minute.

## P2-0 Inputs

| Input | Result |
|---|---|
| **Delivery** | Exchange `b614ee7774e7b29f5f68f5d0df01c05ea932e3f1`; folder final `90b4c3a15…`, checkpoint `e727c64dd…`. Extracted with `git archive`; both manifests pass. |
| **Records tip** | When replayed: `c63ee44f47c72a09545235fddccaa765efd64568`, `TCSlib` tree `745bf4b494b6581a5666ef9ca0a6e735a68ddcef` (U12 and U13 landed). Its Lean differs from B6 only in `GSW/Branching.lean` and `GSW/DecryptFormula.lean`. At the end of the review the tip was `c87eb40365e8ccd44f02ca54f6e5e4f0e50de633`. The changes since are records only: the Lean diff is empty and the `TCSlib` tree is the same. |
| **Snapshot #11** | Map `e7bb03b4…867d0` and files manifest `463c8869…0b13`, both re-hashed. `snapmap.py verify` before the copy: **0/0/0** over 1,487 files, RESULT OK. |
| **Recipe tools** | `olean-advance-a6d01b1b/tools-used/`, copied unmodified from the U12/U13 review. Its 64 hashes are byte-identical to that review's record (`logs/recipe-tools-SHA256SUMS`). |

## P2-1 Heads (scratch only)

- **Worktree.** A detached sparse worktree `$SP/g6b-u1416/wt`, sparse to `TCSlib/`, `TCSlib.lean`, `audits/`,
  `scripts/`, the lake files and `lean-toolchain` (about 34 MB). `.lake/packages` is symlinked to the repository's.
- **Reproduction.** The 2 patches on B6, with `COMMITS.tsv`'s committer data, give `e09ce698…` and then
  **`9852429ef14ce063fcf11ff860e7262f92063d55`**, both as delivered (`logs/repro.log`). There are 0 `gpgsig`, and
  `src/` equals the head byte for byte.
- **Stacked head.**
  - `git merge-tree --write-tree 9852429e c63ee44f` is clean, with tree `b3a0ad09204d1f80f3a50b60e35384cd3522c24b` and
    `TCSlib` tree **`8dc094469b996283c47c3bb5e56587ed1cdd7160`**. That `TCSlib` tree equals the one in the worker's
    information merge with `f46a2ae4` (`72f74525…`).
  - A scratch commit of that tree, with parents tip and head, is **`cf4e56df65741a5b8a468aa57cc28d774d71185a`**. It is
    on no ref (`logs/stack-head.txt`).

## P2-2 Replay at B6 (the `snapshots.md` job recipe; `tools/replay.sh b6 9852429e`)

- **Copy and overlay.**
  - `cp -al $SP/olean-snapshot $SP/g6b-u1416/olean-replay-b6`: 1,487 files, all hard links.
  - `mloverlay.sh` made the Mathlib symlink overlay.
  - `mathlibextra.sh` built `NthRootLemmas` with rc 0, through the slot check. Its olean is **`c0a9cff0…`**, as
    required.
- **Plan.**
  - `downorder.py` at `9852429e` against B6: **changed 2, down 10**. The 10 are the two owned files, `Circular`,
    `LeveledSecurity`, `PolyRatio`, `Asymptotic`, the facades `GSW`, `Homomorphic` and `AdvancedEncryption`, and the root
    `TCSlib`. This is the brief's 9 `UNIT-DOWN` rows plus the root.
  - `fullorder.py` gives 1,456, with roots `TCSlib` and both Checks.
  - `stateplan` plans **10 to build and 1,446 to reuse**.
- **Build.** 01:16:33–01:17:29.
  - **10/10 rc 0.** `error:` 0, `error(` 0, the substring "error" 0.
  - The 8 `sorry` warnings are the 8 targets of U15-U17 and U18-U19 (Circular 1, LeveledSecurity 2, PolyRatio 3,
    Asymptotic 2). There are no other warnings.
  - `Bootstrap` and `Leveled` have empty logs.
  - `Bootstrap` took 9.4 s and every other module 1.9–3.0 s. Peak maxrss was 4.57 GB, for the root.
- **Accept.**
  - `permod.py`: 10 modules, 0 bad, no log/record mismatch.
  - `stateplan update`: 10 modules taken, none refused. This binds every record's source SHA-256 to
    `git show 9852429e:<path>`.
  - `check` over the full order: **1,456/1,456, RESULT OK**. It gives RESULT OK again at the end of the run.
  - **Link count 1:** exactly the 10 rebuilt oleans plus `NthRootLemmas`. Their hashes are unchanged at the end.
  - `snapmap.py verify` after the build: **0/0/0**.
- **Admissions** (`run/b6/admissions.txt`): **35 in 14**.
  - The removed rows are exactly G9, G10, G18, G12 and G13 (`Bootstrap`) and L2 and L3 (`Leveled`).
  - None was added.

## P2-3 Stacked replay on the records tip (`tools/replay.sh stack cf4e56df`)

- **Copy and plan.** A fresh `cp -al` copy with the same overlay. The `NthRootLemmas` olean is hard-linked from the B6
  tree. The plan is **changed 4, down 12**: `Branching`, `DecryptFormula` and the ten above. It gives **12 to build and
  1,444 to reuse**.
- **Build.** **12/12 rc 0**, 0/0 errors and the substring "error" 0. The only warnings are the same 8 `sorry` warnings.
  `Bootstrap` took 10.9 s, and the root peaked at 4.57 GB.
- **Accept.**
  - `permod` reports 0 bad.
  - `stateplan update` takes 12, and `check` gives **1,456 RESULT OK**, also at the end.
  - Link count is 1 for exactly the 12.
- **Admissions:** **26 in 12**. The removed rows are U12's 3, U13's 6 and this unit's 7, and none was added.
- **Cross-check.** `Bootstrap.olean` (`2db3a0e8…`) and `Leveled.olean` (`cb25f0cf…`) are byte-identical to the B6 run's
  (`logs/olean-cross.txt`).
- **Lint at the stack:** see P2-8.

## P2-4 Axioms

`G6bProbe/Axioms` is the U12/U13 census form over `Bootstrap` and `Leveled`. It names the seven targets and
`encrypts_bootGate`, has a `sorry` control, and adds a **`sorryAx` trace**. The trace is a memoized walk of each
constant's dependency closure that lists the constants whose own type or value names `sorryAx`.

- **B6 tree** (rc 0, 14 s; `logs/axioms-b6-summary.txt`).
  - **65 stored constants:** 48 declarations (29 + 18 public, and `bootGate.match_1`) and 17 auxiliaries. The
    auxiliaries are the private `four_pow_clog_le`, its 3 `_proof_` constants, and 13 `_proof_` constants of the new
    proofs. This is the same 65 as the worker's census.
  - **0 axioms outside `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.**
  - **8 constants reach `sorryAx`:** the seven targets and `encrypts_bootGate`.
    - G13's trace is `[decDepth_le]`.
    - The other seven trace through `[depth_nandFormula_le, encrypts_homEvalFormula, maxFanin_nandFormula_le,
      nandFormula_eval]`.
    - Every name is in the brief's allowed U12/U13 set. **0 disallowed, and no owner declaration in any trace.**
      `encrypts_bootGate` traces only through G9's set, as the brief requires.
  - The private helper and every auxiliary are `sorryAx`-free.
  - **Control:** `g6bSorryControl` gives `[sorryAx]`, and its warning is the probe's only warning.
- **Stacked tree** (rc 0, 16 s). The same 65 constants have **0 `sorryAx`**.
  - `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all seven targets and `encrypts_bootGate`.
  - Over the 65 constants, 50 use those three axioms, 6 use `[Quot.sound, propext]`, 8 use `[propext]` and 1 uses none.
  - The control is again `[sorryAx]`.

## P2-5 Rule 10

- **Collector.** `mkcollect.py`, with the two owners, gives `Collect`: rc 0, 668 CAT rows. It reports
  `Bootstrap: stored 40` and `Leveled: stored 25`. The probe source is byte-identical to `mkcollect.py`'s output.
- **Canonical coe-A.** `mkseals_coe.py`, A variant, unmodified, with no chunking needed:

  | Owner | Closure modules | Requests | Active | Already irreducible | Verified | Term names (in closure / excluded) | Result |
  |---|---|---|---|---|---|---|---|
  | `Bootstrap` | 37 | 444 | 426 | 18 | 444 | 35 (22 / 13) | rc 0, 0 errors, 59 s |
  | `Leveled` | 40 | 479 | 461 | 18 | 479 | 41 (27 / 14) | rc 0, 0 errors, 52 s |

  - **Requests.** These are every ordinary TCSlib definition of the closure, matchers included.
  - **Exclusions.** The excluded term names are all `abbrev`s:
    - the structure projections `DAGCircuit.gates`, `.output`, `DAGGate.args`, `.kind` and `LWE.Noise.sample`,
      `.Coins`;
    - `Parameters.columns`, `.lwe`, `.width`, `LWE.Parameters.dimension`, `.modulus`, `.samples`;
    - the notation abbreviations `Ciphertext`, `Coins`, `KeySeed`, `PublicKey`, `Secret`.

    No reducible non-abbreviation definition is in either closure.
  - **Install and EOF masks.** These verified all requests, with 30 and 31 instances removed from unfolding.
- **Seal B** (`SEAL_EVAL=1`): the same requests, since `PolyExpr.eval` is not in either closure. It gives **rc 0 and 0
  errors**, with verified = requested, on both owners.
- **On the stacked tree.** The collector was re-run (rc 0, the same stored counts) and the seals regenerated at
  `cf4e56df`. They have the same request sets, and coe-A and B are rc 0 with 0 errors, 444/444 and 479/479 verified
  (`seal-stack/`).
- **The worker's figure differs by method.** It reports whole-file seals of 298–330 definitions. The canonical
  request sets above are the binding ones (G6B-F11: rebuilt at this base), and they pass.
- **Liveness pairs.**
  - **Method.** The pairs were appended to the canonical sealed copy (sealed) and to the head source (open) with
    `mkctl2.py`. This is the U12/U13 `mkctl.py` plus verbatim `CUSTOM` rows, used for the helper's pairs. NEG reads the
    body (`by intros; first | exact rfl | exact Iff.rfl`, or a concrete `rfl`), and POS goes through the reader.
  - **Where `encrypts_bootGate`'s pairs sit.** `bootGate` is Bootstrap's own definition, which a Bootstrap seal does not
    seal. So the helper's two pairs sit in the sealed copy of `Leveled`, its consumer, where `bootGate` is foreign and
    sealed.

  | Owner | Pair | Sealed | Open |
  |---|---|---|---|
  | Bootstrap | `DAGCircuit.eval` / `eval_eq` (host H19) | NEG line 702: 1 error (Type mismatch); POS 703 passes | 0 errors |
  | Bootstrap | `GSW.decrypt` / `decrypt_eq` (phase-5 `Scheme`) | NEG 706: 1 error; POS 707 passes | 0 errors |
  | Leveled | `bootNoise` / `bootNoise_eq` (Bootstrap) | NEG 568: 1 error; POS 569 passes | 0 errors |
  | Leveled | `DAGCircuit.depth` / `depth_eq` (host) | NEG 572: 1 error; POS 573 passes | 0 errors |
  | Leveled | **`encrypts_bootGate` (1):** `bootGate` at a fan-in-0 gate by `rfl` / through `bootGate_of_args_eq_nil` | NEG 576: 1 error; POS 577 passes | 0 errors |
  | Leveled | **`encrypts_bootGate` (2):** `bootGate` at a fan-in-1 gate by `rfl` / a sealed application of `encrypts_bootGate` to that gate | NEG 580: 1 error; POS 581 passes | 0 errors |

  - Each sealed copy has exactly one error at each NEG line and none elsewhere, so the result is **ALL_OK**
    (`logs/controls-check.txt`).
  - All foreign definitions are among the requests.
- **Explicit-unfold scan.** `unfoldscan.py` resolves every identifier passed to `rw`/`simp`/`simpa`/`unfold`/`delta`/…
  against the 668 CAT rows.
  - At the head it finds 105 identifiers, of which 5 resolve to a TCSlib definition: `unfold bootGate` ×3 and
    `unfold levelGate` ×2. These are the frozen own case readers, identical at the base (17 identifiers, the same 5).
  - The 88 identifiers the fill adds are all theorems, hypotheses or reader calls. **0 foreign definitions.**

## P2-6 Duplication probes

`G6bProbe/DupProbe` runs `exact?` at 400k heartbeats on the tree at the head. Each probe carries exactly the hypotheses
of its use (G53-01).

| Probe | Statement (the fill's use) | Result |
|---|---|---|
| D1 | `1 ≤ y → 2 ^ Nat.clog 2 y ≤ 2 * y` (`four_pow_clog_le`'s `h2`) | fails: no lemma |
| D2 | `1 ≤ y → 4 ^ Nat.clog 2 y ≤ 4 * y ^ 2` (`four_pow_clog_le`) | fails: no lemma |
| D3 | `1 < b → 1 ≤ y → b ^ Nat.clog b y ≤ b * y` (the general form) | fails: no lemma |
| D4 | `((!b).toNat : ℤ) = 1 - (b.toNat : ℤ)` (L3's `hm`) | fails: no lemma |
| D5 | `LWE.sample P χ r = (r.1, LWE.noisyValues P r.1 r.2.1 (χ.sample ∘ r.2.2))` (G12's `hs`) | only `exact rfl`, a defeq read of the foreign `LWE.sample`; no lemma |
| D6 | `decrypt P s (gadget P) = true` (`encrypts_bootGate`'s `hG`) | fails: no lemma |
| D7 | `β ≤ bootNoise P β` (G12's `hle`; `N ≥ 1` by the instance) | fails: no lemma |

- **Hypotheses.** D1–D3 need `1 ≤ y`: at `y = 0`, `Nat.clog 2 0 = 0` and `1 ≤ 0` fails.
- **No D8 for the helper.** A probe of `encrypts_bootGate`'s own statement at the head would find the helper itself.
  The static searches S3/S4 (`logs/dup-searches.txt`) cover it at B6 instead: no per-gate bootstrapping lemma exists.
- **Run.** rc 1 by design, with 6 `exact?` failures and D5's `rfl` suggestion.

## P2-7 Statements and frozen regions (static, recorded here for completeness)

- **decls2** (records copy `fa81981a…`) at the head against B6:
  - **ADDED exactly `encrypts_bootGate`** (`Bootstrap.lean:270`), 0 CHANGED and 0 REMOVED. Leveled is 0/0/0.
  - The helper's statement equals the brief's proposed statement, byte for byte (`logs/helper-statement.txt`).
- **Frozen check, `frozen2.py`.** This is the U12/U13 restore-the-bodies tool, plus the one allowed public insertion
  and its `## Main results` lines. **Both files PASS.**
  - All seven headers and statement-prose regions are byte-identical to B6.
  - Each head normalizes byte-identically to B6 after these steps:
    - the 7 bodies are set back to `sorry`;
    - the 3 refreshed sketches (G10, G13, L2) are set back to B6's;
    - the private `four_pow_clog_le` is deleted;
    - `encrypts_bootGate` is deleted; it must sit directly after G9 and before G10, and it does;
    - its two `## Main results` lines are deleted;
    - both admission sentences are set back.
  - **Controls (`frozen/controls.txt`).** 13 FAIL as required:
    - a one-character header change, in each file;
    - a definition body (`bootNoise`, `levelGate`);
    - statement prose, in each file;
    - a reader body (`bootGate_of_args_eq_nil`);
    - an unpermitted import, in each file;
    - an extra public declaration;
    - the helper moved after G10;
    - another `## Main results` edit;
    - a deleted target (L3).

    Two positive controls PASS: base against itself, and a sketch-only edit.

## P2-8 Lint

`campaign_style_lint.py TCSlib/Cryptography --check8b`:
- **92 FAIL / 103 WARN over 540 files** at B6, at `9852429e`, at the records tip `c63ee44f` and at the stack `cf4e56df`.
- The FAIL/WARN line sets are identical in all four. The only lines naming the owned files are their INFO size lines
  (Bootstrap 349 → 518 lines, 28/0 → 29/1 public/private; Leveled 291 → 384).
- `style_lint.py` on the two owned files gives **0 findings** at B6 and at the head.

## P2-9 State after the run

- **Deleted:** `$SP/g6b-u1416/olean-replay-b6` and `-stack`, after the end-of-run state checks (both RESULT OK, and the
  rebuilt olean hashes are unchanged). The scratch worktree was removed with `git worktree remove`.
- **Snapshot #11:** `snapmap.py verify` gives **0/0/0** at 01:36Z, and again after the deletion.
- **Scratch commits** (on no ref, never pushed): `e09ce698`, `9852429e` (the reproduced worker commits) and the stacked
  `cf4e56df`.
- **Evidence:** `gsw-6b-u14-u16-final-r1-evidence.zip`. The raw seal logs and the sealed copies are included.

## What this changes in `review.md`

| Item | Phase 1 | After phase 2 |
|---|---|---|
| C1/C2 build and admissions | worker's sweep (9 `UNIT-DOWN`, root not built) | **reproduced**: B6 10/10 with the root, 35 in 14; stacked 12/12 with the root, 26 in 12 |
| C5 axioms | worker's census and traces | **reproduced**: 65/65, 8 traces, all allowed; **0 `sorryAx` on the stack** |
| C6 Rule 10 | worker's whole-file seals | **canonical coe-A and B** pass on both heads; 6 liveness pairs, two for the helper; unfold scan 0 |
| Duplication | static | D1–D7 find no lemma |
| New findings | U1416-F01–F05 (static) | none |
