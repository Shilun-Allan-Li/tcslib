# dl-consolidation · rebase r1 over #297 (nm-sim)

**Verdict: ACCEPT.** The landing branch rebases cleanly onto the #297 merge. One more landing edit,
**LE-repoint-nmsim**, re-points the nm-sim files to the consolidated names and pays the first DL-37 item. The build,
statements, axioms and Rule-10 seals all pass.

## Heads

- **Parent:** `2ea4df08d009a4bbdb8042795ff062d7f22db325`, the records tip after the #297 merge
  `758a103030728b7b6bd13bc2ca400173ee49bf58`.
- **Head:** `6f853adc61d5d175ee83c69f6c07ab2da112cabc`, tree `aa4e3e0cad4322fc8af156e399da55fbfa3a552f`.
- **The 8 rebased commits:** they keep their authorship. `range-diff.txt` shows each identical in content.

  | Commit | Content |
  |---|---|
  | `132b37c086b38e3ad677b387d6400765163c076a` | checkpoint 1 |
  | `ae24e7ec2dc783d13732872d7e4243093575223a` | checkpoint 2 |
  | `9c0023b8f7c2e6a8d68d0e9ea5bcf529270cf6fe` | checkpoint 3 |
  | `dce2820246b6736c3d7b8ef3abd8bf74460766f8` | R3/R4/Eager |
  | `406b8d57286050dc1f91cd9b3e8e6d9665f48afc` | LE-split |
  | `06fab4358e678b2ff092e5f1f3a544a3db9e635e` | LE-repoint |
  | `82f8d1bc1e6b9e89893d6c6f4dc799fe9313bb4c` | LE-review |
  | `510e9d755bd110f98624a6b15a7bfbd12bf999fc` | LE-rule10 |

- **The rebase itself:** it had no conflict. On `TCSlib/` and `audits/`, the change from the old head `7b7d07aa` to
  the rebased 8th commit equals #297's own change (`rebase-check.txt`).

## LE-repoint-nmsim (`6f853adc`)

This edit touches 8 of the 11 nm-sim files. It changes proofs and `open` lines only (`landing-edit-LE-repoint-nmsim.patch`;
counts in `repoint-counts-final.txt`).

- **Removed `open` lines.** The selective `open AdaptiveCPA (…)` lines go from `Simulation`, `SimIND`, `IndSim` and
  `Simulator`.
- **Re-pointed names.**
  - `castImpl_eq`, `expect_simulate_castImpl_toCompOn`, `padFin_ofFn_zeroBits` and `simulate_eq_of_abs` → `Games.*`.
  - `ofFn_splitHalf_fst`/`_snd` → `FixedLengthScheme.*`.
  - `expect_sample_equiv`/`_comm` and `expect_sub` → `ProbComp.*`.
  - `GGMRed.ofFn_padFin_of_length` → root, at 25 sites.
- **DL-37 (first item paid).** The private `NMSim.padFin_replicate_false` in `Simulation/Challenge.lean` is
  deleted. Its one use now reads `Games.padFin_replicate_false`.
- **Unchanged statements.** The statements of `castImpl_snmImpl` and `castImpl_indImpl_abs` keep the unqualified
  spelling `castImpl`, which resolves to `Games.castImpl` through the existing `open TCSlib.Cryptography.Games`.
  Their text is byte-identical.
- **Width.** Five lines were re-wrapped. No line is over 100 characters.

## Checks

**Statements**
- decls2 over the 11 nm-sim files from `758a1030` to the head: **0 rows**.
- `touched`: 1 REMOVED (the private lemma), 29 proof-only changes, 322 unchanged.
- **Evidence correction.** The `statements/decls2-nmsim.tsv` in the evidence zip was written 39 seconds before the
  amend that restored the `castImpl` spelling. It shows the 2 pre-amend rows. I re-ran decls2 at the head; the
  result is in the zip under `statements-r2/`, with its own `SHA256SUMS`. That re-run is authoritative.
- decls2 over all 51 Lean files changed from the parent to the head: 68 ADDED, 42 REMOVED, 2 MOVED, **0 CHANGED**
  (`decls2-pr.tsv`).

**Build**
- Rebuilt on the consolidation's full tree, 15 modules: the 10 nm-sim helpers, `Simulation`, the `PublicKey` and
  `Encryption` facades, `Composability`, and root `TCSlib`. All 15 have rc 0.
- All 1198 TCSlib/`audits` modules end with rc 0 at the final-head source hash.

**Axioms**
- The 572 stored constants of the nm-sim files use only `propext`, `Classical.choice` and `Quot.sound`.
- All 16 endpoints print `[propext, Classical.choice, Quot.sound]` (`axioms-summary.txt`):
  - nm-sim's 3 endpoints;
  - the consolidation's 10;
  - #294's 3.

**Rule 10**
- Whole-file seals of the 11 nm-sim files: A 11/11, B 11/11.
- Paired controls: ALL_OK, 38 sealed negatives.
- The consolidation's seal table (34/41 A, 30/41 B; 0 new failures) still holds. None of its 41 sealed owners has
  a file or TCSlib closure containing a module changed since `7b7d07aa` (`consolidation-seal-closure-check.txt`).

**Admissions**
- 219 warnings, down 2.
- Issued modules: 45 = base 48 − #294's 1 − nm-sim's 2.
- 174 lie outside the issued order, unchanged.

**Lint against the new parent**
- FAIL 214 → 216, WARN 103 → 103.
- The delta is the same as before the rebase:
  - +4 FAILs from the PaddedCPA split, as already accepted;
  - −2 FAILs from deleting `Eager`;
  - ElGamal's size WARN now reads 1830 lines.
- nm-sim adds nothing.

**Sizes:** every nm-sim file is under 1000 lines; the largest is `SimIND`, at 912.

## Evidence

- **`rebase-evidence.zip`** (SHA-256 `d9ab3700f4c91b0856c526769c8eaaccd014c8fb94d4709516c645c6663cc5e0`).
  - It holds the rebase-r1 directory without the raw seal sources and controls records, which were left out for
    size.
  - Its `SHA256SUMS` (SHA-256 `da4ad8b3d1039bbf534db467b91b1062dcf0e65e3abf782a9662b9dbb60c4bf5`, 188 entries,
    verified) covers the whole directory, including the excluded raw files.
  - It does not cover `statements-r2/`, which carries its own manifest.
- **Extracts in this folder:**
  - the patch;
  - `range-diff.txt` and `rebase-check.txt`;
  - the re-point counts;
  - the axioms;
  - the seal tables;
  - the closure check;
  - the census;
  - the lint diff;
  - `decls2-pr.tsv`.

## Debt now foldable (not done here)

These items are in the DL-37 and DL-36 payback for the post-consolidation window:

- `Rounds.rdU`, `rdZ`, `rdW`, `rdState`, `rdIdx`, `rdQuery`, `rdLog` and `Simulator.finSt` are identical to the published
  `InteractiveHandler.rU`, `rZ`, `rW`, `rS`, `rI`, `rX`, `rL`.
- `Rounds.impl_of_ret` → `InteractiveHandler.impl_of_ret`.
- `NMSim.ofFn_padFin_eq_padL` (public, `Rounds.lean`; disclosed in DL-37) is the A4 lemma
  `EnsembleLemmas.ofFn_padFin_eq_padL`. The ledger row now names that counterpart.
- `ChallengeSim.expect_simulate_eager` can be derived from `NMSim.expect_simulate_eager`.
- `rdAns` is a fourth copy of `rFwd`, `rY` and Forward's `rAns`. The ledger row now names it.
- The DL-36 items listed in `../review.md`.
