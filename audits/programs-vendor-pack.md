# External audit pack: the vendored programming layer `TCSlib/Programs/` (fidelity gate)

**Campaign context.** This is the Arora–Barak ch3–4 campaign (`AroraBarakChapters3-4Plan.md`;
design `machine-library-design.md` §14–§15b). On 2026-10-12 the user commissioned a programming
layer ("language first") and chose to *port* an existing one ("Port it"). The source is the
light language, its program logic, its verified routines, its compiler and its word RAM, from
**[AFM26]**: `https://github.com/anthropics/formal-math`, folder `3sum-apsp`, commit
`e1a4e6508154ea59f030480661590a9fe3018011` (Apache-2.0, © Anthropic, PBC). The port is PR #62,
branch `vendor/light-programs`. **The code under audit is commit
`eea1dedb1f0ae73b7debc8ce45af693a24ffe10d`**; this pack's own commit adds only `audits/` files.

**What this gate is for.** It is a *fidelity* gate. Lean's kernel has already checked every
vendored proof at our pin (the replay below). The mathematics is upstream's and is not under
audit. What is under audit is whether the port is **faithful**:
- each vendored file is its upstream original plus *exactly* the local modifications its header
  lists;
- no statement has changed except by the listed renames;
- attribution and licensing are complete;
- the records describe the port truthfully.

The gate closes on zero blockers and zero majors.

## What was vendored

There are 41 upstream files. 40 are under `3sum-apsp/ThreeSumApsp/`, and one is
`3sum-apsp/EndStatement.lean`. They land under `TCSlib/Programs/`:

| Upstream | tcslib |
|---|---|
| `Lang/` (language, logic, tactics) | `TCSlib/Programs/Light/` |
| `Lang/Lib/` (14 routines; `Sieve` deferred) | `TCSlib/Programs/Light/Lib/` |
| `Lang/Compiler/` (compiler to the word RAM) | `TCSlib/Programs/Light/Compiler/` |
| `EndStatement.lean` (trimmed to the word RAM), `Machine/Steps.lean` | `TCSlib/Programs/WordRAM/Basic.lean`, `.../Steps.lean` |
| `Util/` (six helper modules) | `TCSlib/Programs/Util/` |

The per-file map is `audits/evidence/programs-vendor/file-map.md`. Hashes are in
`audits/evidence/programs-vendor/upstream-manifest.md`, which lists, for every file, its upstream
git blob id and SHA-256 and the vendored blob id at the code commit. The upstream originals are
attached byte for byte under `audits/evidence/programs-vendor/upstream/`, with a `.txt` suffix.

The maintainer also wrote these files. They are tcslib's own, not vendored:
- `TCSlib/Programs/Compat.lean`: three names that differ at our Mathlib pin, each proved;
- the facades `TCSlib/Programs.lean`, `TCSlib/Programs/{Util,WordRAM,Light}.lean`;
- the repository `NOTICE`;
- edits to `TCSlib.lean` (root import), `TCSlib/ComputationalModels.lean` (two models
  registered) and `scripts/campaign_style_lint.py` (the vendored files registered);
- the generator `scripts/vendor_afm26/`.

## The listed modifications (each file's header lists the ones that apply to it)

| # | Class | Where | Rationale |
|---|---|---|---|
| M1 | The Lean module-system syntax removed: `module`, `public import` → `import`, and `@[expose] public section` / `public section` → `section`; scopes still open at EOF are closed explicitly | all 41 | our pin is v4.25.0. Precedent: the vendored cslib files (`TuringMachine/Deterministic.lean`, header) |
| M2 | Moved and imports remapped: `ThreeSumApsp.X` → `TCSlib.Programs.…` (table above) | all | placement (design §15b) |
| M3 | Namespaces renamed: `EndStatement` and `ThreeSumApsp.WordRam` → `WordRAM`, and `ThreeSumApsp` → `Light`; module names and paths in comments updated | files that contain them | the paper-specific names `EndStatement`/`ThreeSumApsp` do not belong in tcslib |
| M4 | `EndStatement.lean` trimmed to `Instr`, `exec` and `loadWords`; its paper problems and claims (`BigO`, `Problem`, `Problem.SolvedBy`, `Problem.SolvedInTime`, `rowByRow`, `ExactTriangle`, `ε_T`, `Theorem_19`, `ThreeSum`, `Theorem_22_3SUM`, `MinPlusProduct`, `Theorem_22_MinPlus`, `Path`, `APSP`, `Theorem_22_APSP`, `ZeroWeightKClique`, `Corollary_39_ZeroWeight`) dropped, and its module docstring rewritten | `WordRAM/Basic.lean` | only the machine is needed |
| M5 | A `## References` section citing [AFM26] added to the module docstring | all | `policy.md` §2 (file-level references; the lint) |
| M6 | The repository-standard `set_option` header added | all | `policy.md` §1 |
| M7 | The tactic combinator `with_unfolding_none` (absent in v4.25) replaced by `with_reducible`, 2 occurrences | `Light/Tactics.lean` | Lean-version gap. An approximation: reducible definitions may now unfold where upstream unfolds none |
| M8 | Nine v4.25 proof repairs (list below); proof bodies only | 7 files | Lean-core behaviour differences |
| M9 | `import TCSlib.Programs.Compat` added | `Util/List`, `Light/Compiler/Cells`, `Light/Lib/MergeSort` | three names absent at our pin |
| M10 | `import Batteries.Data.Nat.Lemmas` added | `Util/Index` | upstream reaches `Nat.mul_add_lt_mul_of_lt_of_lt` through its Mathlib v4.33 imports; ours does not (found by the first replay) |
| M11 | A vendoring header added inside the upstream copyright comment: source, commit, and the list of modifications | all | `policy.md` §2, vendored code; Apache-2.0 §4(b) |

**The nine proof repairs (M8),** from `scripts/vendor_afm26/fixes.py`, each applying exactly once:

| # | File | Upstream text | Replacement | Reason |
|---|---|---|---|---|
| R1 | `Util/List` | `List.getD_of_forall_mem (p := fun x => \|x\| ≤ U) (by rwa [abs_zero]) h i` | `… (by simpa using hU) h i` | v4.25 leaves the instantiated motive `(fun x => \|x\| ≤ U) 0` unreduced, so `rwa` misses |
| R2–R3 | `Light/Lib/Logs` | `rw [show 2 ^ (i + 1 + 1) = …]` and `rw [show 2 ^ (i + 1) = …]` | `beta_reduce` inserted before each | the loop rule's invariant stays applied to its round, unreduced |
| R4 | `Light/Lib/CountSort` | `rw [show A.nb - (r + 1) = s by omega]` | `beta_reduce` inserted before | as R2 |
| R5–R6 | `Light/Lib/Emod` | `rw [hnext]` and `rw [show emodRounds a Mo - (i + 1) = c by omega]` | `beta_reduce` inserted before each | as R2 |
| R7 | `Light/Lib/Sqrt` | `rw [show (i + 1 + 1) * (i + 1 + 1) = …]` | `beta_reduce` inserted before | as R2 |
| R8 | `Light/Compiler/Cells` | `· simp [Int.toNat_of_nonneg hnonneg]` | `· rw [Function.update_apply, if_pos (by omega)]` then `simp` | v4.25's `simp` does not rewrite the cast `↑a.toNat` in that position, and leaves a structure projection unreduced |
| R9 | `Light/Compiler/CallFrames` | `split_ifs <;> rw [Function.update_of_ne (by cells), A.cell (by cells)]` | `… <;> simp [*]` appended | v4.25's `split_ifs` leaves the `if` inside the argument of `m` |

**The three compatibility names (M9),** in `TCSlib/Programs/Compat.lean`, all proved:
- `List.map_coe_finRange_eq_range`, from our `List.map_coe_finRange`;
- `List.Pairwise.merge`, from core's `List.sorted_merge`;
- `Set.mem_ofPred_eq`, which is `rfl`, like our `Set.mem_setOf_eq`.

Each is to be removed at the Mathlib bump that provides it (backlog PROG-1).

**Not vendored:**
- `Lang/Lib/Sieve.lean`, which needs `Nat.primesLE`, absent at our pin (PROG-1);
- everything that depends on the paper's statements: `PaperStatements.lean`, `Lang/WordSize`,
  `Lang/RowMajor`, `Machine/Solving`, `Lang/ToMachine`;
- the paper's programs, `Programs/`.

## Brief for the auditor

Work from the attached files. If you can reach GitHub, also check the upstream copies against
the upstream commit; the manifest's blob ids make that mechanical.

1. **Provenance.** Confirm that the attached upstream copies are the upstream files: by blob id
   against GitHub if you can, otherwise by internal consistency with the manifest. Confirm that
   the vendored files in the bundle are those at the code commit (manifest, vendored blob ids).
2. **Fidelity, file by file.** Use `audits/evidence/programs-vendor/upstream-to-vendored.diff`,
   or diff the attached pairs yourself. Check that **every** change from an upstream file to its
   vendored file falls in one of M1–M11 and is listed in that file's header. Report any change
   that is unlisted, or listed but absent. Spot-check that the bundled diff matches the attached
   pairs.
3. **Statements unchanged.** Confirm that no declaration's statement (signature, type, or
   definition body for `def`/`abbrev`/`structure`/`inductive`) changed, except by the M3 renames.
   Confirm that R1–R9 touch proof bodies only. Confirm that no declaration was added or removed
   from a vendored file, apart from M4's listed drops.
4. **The repairs.** For each of R1–R9, judge whether the replacement is a faithful local repair:
   the same statement, proved by a step that does what the upstream step did. Kernel acceptance
   is attested below, so the question is fidelity and reviewability, not soundness.
5. **The tactic swap (M7).** Assess the consequences of `with_unfolding_none` → `with_reducible`
   in the `light_*` macros. Tactics cannot affect soundness. Say whether the swap can change what
   a vendored *statement* says (it should not: tactics appear only in proofs), and whether a note
   is warranted for future users of the tactics.
6. **The trim and the exclusions (M4, Sieve).** Confirm that no retained file uses a dropped
   declaration, that `WordRAM/Basic.lean`'s rewritten docstring is accurate, and that the
   exclusion list is complete and truthful.
7. **The renames (M3).** Check them for consistency and completeness:
   - no stray `ThreeSumApsp` or `EndStatement` in code;
   - no name capture or collision (the replay and the name screen are attested below);
   - whether root-level `Light` and `WordRAM` namespaces fit `policy.md` §1 (area-local namespace
     roots; the model-registry exception for model types).
8. **Attribution and licence.**
   - Each vendored file keeps the upstream copyright notice and states its changes (Apache-2.0
     §4(b)–(c)).
   - The repository `NOTICE` reproduces the upstream `NOTICE` verbatim (§4(d)), and its statement
     of which files are vendored is accurate.
   - `Compat.lean` and the facades carry tcslib headers and cite [AFM26] where they draw on it.
9. **Wiring and records.**
   - The facades import every module (the lint's facade rule).
   - `TCSlib.lean` imports the area.
   - The two `ComputationalModels.lean` entries describe the models correctly.
   - The lint's vendored list contains exactly the 41 vendored files.
   - Design §15b, the decision-log rows and backlog PROG-1 state the port truthfully.
10. **The generator (optional).** `scripts/vendor_afm26/` is attached. Say whether the diff is
    what the scripts produce from the upstream files and `fixes.py`, as far as you can tell by
    reading them.
11. Report anything else that the records misstate.

## Repository-side attestations (verify or challenge)

The maintainer executed these. The logs are attached.

- **Replay** (user-run, at `155255ed`). That commit differs from the code commit in records only,
  plus one comment line: `git diff 155255ed eea1dedb -- TCSlib` is the one-line correction to
  `WordRAM/Basic.lean`'s module docstring. That line had named the upstream file `WordRAM.lean`, an
  artefact of the M3 rename. The file's closure check was re-run clean after the correction. It compiled each of the 42 modules, the four
  facades and `ComputationalModels` separately, in dependency order, with fresh `.olean`s
  (`audits/logs/programs-vendor-replay.log`).
  - **47/47 clean, 0 errors, no `sorry` warnings.**
  - The first run failed 17 modules: `Util/Index` (M10), plus the 16 that depend on it. The fix
    is M10. The resumed run compiled the 17 and skipped the 30 that were clean.
- **Per-module closure check** (`audits/logs/programs-vendor-closure-check.log`). Each of the 46
  modules and facades was elaborated read-only over exactly its own import closure: **46/46
  clean.** This check exists because the first, concatenated check imported the union of every
  file's imports, and that union masked M10's missing import.
- **Census and axioms** (`audits/logs/programs-vendor-elab.log`; the concatenated shipped files,
  elaborated together with all fifteen `Complexity` facades and `ComputationalModels`, before
  M10, which adds an import only).
  - 0 errors.
  - 2,990 constants declared, none using `sorryAx` directly, and no `axiom`.
  - `Light.Compiler.compileProgram_correct` and `Light.sort_meets` depend on
    `[propext, Classical.choice, Quot.sound]`.
- **Name screen** (`audits/logs/programs-vendor-namescreen.log`). There are 713 new public names.
  The areas outside `Complexity` (3,966 names) were screened textually, with no clash. The
  `Complexity` library is covered exactly by the joint elaboration above.
- **Lint** (`audits/logs/programs-vendor-stylelint.log`, at the code commit): 0 FAIL, 0 WARN over
  45 files.
- **Upstream copies.** All 42 attached upstream files match their manifest blob ids
  (`git hash-object`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is that of `audits/TEMPLATE.md`. Findings go verbatim into
`audits/programs-vendor-findings.md`. The gate closes when it has zero blockers and zero majors.
