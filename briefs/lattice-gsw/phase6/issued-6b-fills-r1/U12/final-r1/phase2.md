# GSW 6b U12 `gsw-6b-u12` · final r1 · phase 2: replay on olean snapshot #11

**Verdict: PASS, with no new finding.** One replay tree carried U12 and U13 stacked (U12, then
U13). This is the order README *Landing order* gives, and the two files are disjoint. Each unit was
then replayed **alone** on its own copy of the snapshot. `GSW/Branching.lean` compiles at B6 + U12
and at B6 + U12 + U13, and its olean is byte-identical in both.

- **Build.**
  - **Stack:** 12/12 modules rc 0, including the root `TCSlib`. There were 0 `error:`/`error(`, the
    substring "error" occurs 0 times, and no warning other than the 15 `sorry` warnings of other
    units' targets.
  - **U12 alone:** 11/11 rc 0, with admissions **39 in 15** = `base-sorries.txt` minus G1–G3.
  - **Checks.** No `audits/*/Checks` imports a changed module. Both are in the full order, reused,
    and pass the state check.
- **Axioms.** All 13 stored constants of `Branching` use only `propext`, `Classical.choice` and
  `Quot.sound`. There is 0 `sorryAx`, and each target is `[propext, Classical.choice, Quot.sound]`
  in both the census and `#print axioms`.
- **Seals.** Canonical coe-A and seal B: rc 0 with 0 errors, 200 requested and 200 verified.
- **Controls.** 2 liveness pairs, ALL_OK.
- **Unfold scan.** 0 foreign definitions.
- **Duplication probes.** No lemma found.
- **Lint.** Unchanged.
- **Snapshot #11.** Rehashes 0/0/0 before, after the build and at the end.

Run on 2026-11-18 from 22:28 to 22:42 UTC. `$SP` is
`/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`. The work
directory is `$SP/g6b-u1213/`.

- **Lean processes.** One at a time: 46 starts plus `mathlibextra`.
  - Each start went through `runq.sh`, which checks before the start that at most 2 other Lean
    processes are running (`pgrep -fc "bin/lean "`) and at least 2,000 MB is free. Each start is
    logged in `logs/slot.log`.
  - There was never more than 1 other Lean process on the host, and no start waited.
  - The lowest free disk at a start was **2,771 MB**.
- **Not done.** No `lake build`, no cache get, no commit, no branch, no push, no PR.
- **Not touched.** The snapshot was read and hard-linked only. No existing `$SP/olean-replay-*`
  tree was touched, and no other job's process.
- **Deleted at the end:** my three replay trees (stack, U12 alone, U13 alone). Each can be rebuilt
  in about a minute.

## P2-0 Inputs

| Input | Result |
|---|---|
| **Records tip** | `31247fe71e7ab60a1d7f8f1939291147e1b5645a` (`cryptography/pass-shelat-ch2-4`, checked out). It is Lean-equal to B6 = snapshot #11's T: the `git diff --name-only` over `TCSlib`, `TCSlib.lean`, `audits`, the lake files and `lean-toolchain` is empty. |
| **Delivery** | `9b4ab065f58581ac93ba6641f29a0d4051482dfa`, which equals `origin/exchange/pass-shelat-ch5-8`. Extracted with `git archive`; both manifests pass. |
| **Snapshot #11** | Map `e7bb03b4…867d0` and files manifest `463c8869…0b13`, both re-hashed. `snapmap.py verify` before the copy: **0/0/0** over 1,487 files, RESULT OK. |
| **Recipe tools** | `olean-advance-a6d01b1b/tools-used/` from `olean-rebase-evidence.zip` (`b662b7da…`), unmodified. They are byte-identical to EF-H12's copy (64 files; `logs/recipe-tools-SHA256SUMS`). |

## P2-1 Heads (scratch only)

- **Worktree.** A detached sparse worktree `$SP/g6b-u1213/wt`, sparse to `TCSlib/`, `TCSlib.lean`,
  `audits/`, `scripts/`, the lake files and `lean-toolchain`. `.lake/packages` is symlinked to the
  repository's.
- **Reproduction.** The 2 patches on B6 give `f0a51d1e…` and then `afdaa9e2…`, both as delivered
  (`logs/repro-u12.log`).
- **Check head.** The U13 patch applied by `git am` on `afdaa9e2` (unsigned, committer date
  `2026-11-18T12:00:00Z`) gives **`51d46089e37030f582b24c1f84ee68ac21c98829`**, tree
  **`fb6884d14882417682957ee056aab4bf6376652c`**.
  - That tree equals `git merge-tree --write-tree afdaa9e2 74fb355a`.
  - Its diff against B6 is exactly the two owned files, +157/−20.

## P2-2 Replay of the stack (the `snapshots.md` job recipe)

- **Copy and overlay.**
  - `cp -al $SP/olean-snapshot $SP/g6b-u1213/olean-replay`: 1,487 files, all hard links.
  - `mloverlay.sh` made 3,346 Mathlib symlinks.
  - `mathlibextra.sh` built `NthRootLemmas` with rc 0. Its olean is **`c0a9cff0…`**, as required.
- **Plan.**
  - `downorder.py` at `51d46089` against B6: **changed 2, down 12**. The 12 are the two owned files,
    `Bootstrap`, `Circular`, `Leveled`, `LeveledSecurity`, `PolyRatio`, `Asymptotic`, the facades
    `GSW`, `Homomorphic` and `AdvancedEncryption`, and the root `TCSlib`.
  - **No `audits/*/Checks` imports any of them.** Both Checks import 4–5 other modules.
  - `fullorder.py` gives 1,456, with roots `TCSlib` and both Checks.
  - `stateplan init` at B6 gives 1,456 modules, and `plan` gives **12 to build and 1,444 to
    reuse**.
- **Build.** 22:29:27–22:30:00.
  - **12/12 rc 0.** `error:` 0, `error(` 0, the substring "error" 0.
  - The 15 `sorry` warnings are the 15 targets of U14-U16, U15-U17 and U18-U19 (Bootstrap 5,
    Circular 1, Leveled 2, LeveledSecurity 2, PolyRatio 3, Asymptotic 2). There are no other
    warnings.
  - `Branching` and `DecryptFormula` have empty logs.
  - Times were 1.6–3.0 s per module. Peak maxrss was 4.58 GB, for the root.
- **Accept.**
  - `permod.py`: 12 modules, 0 bad, no log/record mismatch.
  - `stateplan update`: 12 modules taken, none refused. This also binds every record's source
    SHA-256 to `git show 51d46089:<path>`.
  - `check` over the full order: **1,456/1,456, RESULT OK**. It gives RESULT OK again at the end of
    the job.
  - **Link count 1:** exactly the 12 rebuilt oleans plus `NthRootLemmas`. Their hashes are
    unchanged at the end.
  - `snapmap.py verify` after the build: **0/0/0**.
- **Admissions at the stack.** `base-sorries.txt` with the rebuilt rows replaced by the build logs
  gives **33 in 14**. The removed rows are exactly G1–G3 and U13's six, and none was added
  (`logs/admissions-stack.txt`).

## P2-3 U12 alone

`alone.sh u12 afdaa9e2`:
- **Copy and plan.** A fresh `cp -al` copy with the same overlay; the `NthRootLemmas` olean is
  hard-linked from the stack tree. The plan is changed 1, down 11, **11 to build and 1,445 to
  reuse**.
- **Build.** **11/11 rc 0**, 0/0 errors; the 15 `sorry` warnings are again other units' targets.
- **Accept.** `stateplan update` takes 11, and `check` gives **1,456 RESULT OK**. Link count 1 for
  the 11.
- **Admissions:** **39 in 15**. Only G1–G3 are removed, matching the brief's C2 count.
- **`Branching.olean` here equals the stack's** (`aa01dfa1…`, `logs/olean-cross.txt`).
- The copy was deleted after its records were kept (`alone/u12/`).

## P2-4 Axioms

`G6bProbe/Axioms` is the recipe's census form, over the `Branching` and `DecryptFormula` modules,
with the nine targets by name and a `sorry` control. It gives rc 0 in 8 s.

- **`Branching`: 13 stored constants**, the same 13 as the worker's `AxiomProbe-final.log`, with
  the same sets.
  - 10 are `[Classical.choice, Quot.sound, propext]`: the 9 named declarations and the private
    glue, which the census tags as an auxiliary because its name is internal.
  - `Encrypts.select._proof_1_1` and `._proof_1_2` are `[Quot.sound, propext]`, and
    `homEvalFormula._proof_1` is `[propext]`.
  - **0 non-standard, 0 `sorryAx`.**
- **Targets.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for G1, G2 and G3.
- **Control.** `g6bSorryControl` gives `[sorryAx]`, and its warning is the probe's only warning.

## P2-5 Rule 10

- **Collector.** `mkcollect.py`, with the two owners, gives `Collect`: rc 0, 606 CAT rows. It
  reports `Branching: stored 13` and `DecryptFormula: stored 23`.
- **Canonical coe-A.** `mkseals_coe.py`, A variant, unmodified, with `SEAL_CHUNK=1000` (not
  triggered):
  - **200 requests.** These are every ordinary TCSlib definition of the closure, matchers
    included.
  - 24 term names, of which 14 are in the closure and 10 are excluded abbreviations: `Instr.map0`,
    `map1`, `var`, `instrs`, `Ciphertext`, `Parameters.columns`, `lwe`, `width`, and
    `LWE.Parameters.dimension`, `modulus`.
  - **Result: rc 0 and 0 errors in 18 s.** `G06-SEAL requested=200 active=182
    already_irreducible=18 verified=200` and `G06-SEAL-END … verified=200`.
- **Seal B** (`SEAL_EVAL=1`): the same 200 requests, since `PolyExpr.eval` is not in this closure.
  It gives **rc 0 and 0 errors**, with verified 200 = requested.
- **The worker's figure agrees.** It also has 200 requests (census 945).
- **Liveness pairs.** These were appended to the canonical sealed copy (sealed) and to the head
  source (open), with `mkctl.py`. NEG reads the body (`by intros; first | exact rfl | exact
  Iff.rfl`), and POS uses the reader.

  | Pair | Sealed | Open |
  |---|---|---|
  | `BranchingProgram.evalWith` / `evalWith_eq` (6a host) | NEG line 451: 1 error (Type mismatch); POS 452 passes | 0 errors |
  | `GSW.mul` / `mul_eq` (phase-5 `Noise.lean`) | NEG line 455: 1 error; POS 456 passes | 0 errors |

  - Sealed: exactly 2 errors, one at each NEG line, so the result is **ALL_OK**.
  - Both definitions are among the 200 requests.
- **Explicit-unfold scan.** `unfoldscan.py` resolves every identifier passed to
  `rw`/`simp`/`simpa`/`unfold`/`delta` against the 606 CAT rows.
  - `Branching`: 28 identifiers, 0 TCSlib definitions.
  - All are theorems, local hypotheses, or a `show` term.
  - The proofs pass no definition to `simp` or `rw`.

## P2-6 Duplication probes

`G6bProbe/DupProbe` runs `exact?` with 400k heartbeats:
- **D1** (G2's `Pi.single`/`decide` fact): `exact?` fails. No lemma.
- **D2** (an instruction of a permutation program is a permutation): the only suggestion is
  `exact hB ι h`. That is a defeq read of the foreign `IsPermutation`, not a lemma. The delivered
  reader composition is the right form.
- The run is rc 1 by design, with 4 `exact?` failures in all (D3 and D4 are U13's).

## P2-7 Lint

`campaign_style_lint.py TCSlib/Cryptography --check8b` on the worktree:
- **92 FAIL / 103 WARN over 540 files** at B6, at `afdaa9e2`, at `74fb355a` and at the stack.
- The FAIL/WARN line sets are identical in all four. The only lines naming `Branching` are its
  INFO size line (179 → 268).
- `style_lint.py` on the two owned files gives **0 findings** at each head.

## P2-8 State after the run

- **Deleted:** `$SP/g6b-u1213/olean-replay`, `-u12` and `-u13`, after the end-of-run state check.
- **Snapshot #11:** `snapmap.py verify` gives **0/0/0** at 22:42Z.
- **Kept:** the scratch worktree `$SP/g6b-u1213/wt` until the evidence was zipped. Then it was
  removed with `git worktree remove`.
- **Scratch commits** (on no ref, never pushed): `f0a51d1e`, `afdaa9e2`, `74fb355a` and
  `51d46089`.
- **Evidence:** `gsw-6b-u12-u13-final-r1-evidence.zip`. The raw seal logs and the sealed copies are
  included, since they are small.

## What this changes in `review.md`

| Item | Phase 1 | After phase 2 |
|---|---|---|
| C1/C2 build and admissions | worker's sweep (10 modules, root not built) | **reproduced**, with the root `TCSlib` in the stack and U12 alone; 39 in 15 |
| C5 axioms | worker's census | **reproduced**: 13/13, same sets |
| C6 Rule 10 | worker's whole-file seals | **canonical coe-A and B** pass; 2 liveness pairs; unfold scan 0 |
| Duplication | static | `exact?` probes D1/D2 find no lemma |
| New findings | none | none |
