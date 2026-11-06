# External audit pack, round 2: dedup AS-1, proofs that unfold `astep` (PR #214, a dedup gate)

**Round 1** (`pack.md`, `findings.md`, `resolutions.md`) was **HOLD: 0 blockers, 1 major, 0
minors**. The targeted rewrite of `astep_call₁` passed (note 2). Finding 1 (major) was about
completeness: the family went far beyond the three named lemmas. It covered named
single-instruction continuations, inline instruction equations and macro expansions, counted one
member per containing declaration, and `TQBFARM/Leaf` alone crossed the one-fifth threshold.

**The user ruled (2026-11-06): all of it in #214.** A by-kind scope
(`campaign/items/dedup/as1-SCOPE.md`) found **181 containing declarations in 40 files**. Its
search covered every closing form outside `Machines/ARM`: `simp`, `simp only`, `simpa`,
`simpa only` with `astep`, the scoped `regs [astep, …]` macros, and PathHard's `stp` macro, whose
body was `simp only [astep, A, …]`. Of those, 8 are excluded as machine comparisons, leaving 173
in scope. Round 1's four "colleague-owned" circuit lemmas, and the fifth, are also in: the user's
2026-11-06 ruling allows mechanical edits in colleague files.

**The PR:** #214 on `lean/dedup-as1`, head `92e53e6e` (full hash in the bundle header). It
consists of:
- round 1's `0bc71211`;
- `1fd7d4ce`: the five circuit equations re-proved through the general ones;
- `1856e771`, `5fdcfcf4`, `090fcccd`, `29c41e09`: the first 43;
- `acde1f4e` … `fa1673aa`: the remaining 130, one commit per directory;
- a merge of the campaign after #216.

It changes 38 Lean files: 725 lines added, 567 removed (`evidence/round2/landing/as1-merged.diff`).

## What changed since round 1 (verify)

| Finding | Change |
|---|---|
| 1 | **Fixed in full.** Every in-scope declaration now closes its steps through the published equations: `astep_inc`, `dec`, `clr`, `half`, `jz`, `jodd`, `jeq`, `call`, `ret`, `valP`, `valQ`, `jeqIn`, `jeqFst` and `jeqSnd`, or a derived one (`LogProg.astep_call₁`; AdjScan's `astep_rd`/`astep_hit`/`astep_jeqFst`; AdjWalk's `astep_call₁`/`astep_call₂`). The forms used are listed below. In all, **501 sites** in the 173 declarations, plus 3 caveat declarations. |
| 3 (note) | `UnaryLogspace`'s `LtM.loop` and `ltLang_mem` (`astep_jeqIn`, `astep_inc`, `astep_valP`), in `5fdcfcf4`. |
| 4 (note) | Superseded. The five circuit members are re-proved (`1fd7d4ce`). |

**The forms used:**
- `astep_<kind> h`, when an instruction hypothesis is available.
- `astep_<kind> (show M .l = _ from rfl)` on a concrete machine. Long decision terms are written
  as placeholders, e.g. `(.rt _)`.
- `astep_<kind> (A := fun _ => Ins.<kind> _ …) rfl` for ExpBFS's deterministic part. A bare
  `(A := fun _ => _) rfl` does not unify there.
- A local `have` stating the instruction once (`pm_run`, `CounterProgSim`), following those files'
  existing `hcall` idiom.
- `cond_true`/`cond_false`, `if_pos`/`if_neg` and `dif_pos`/`dif_neg` for `bif`/`if`/`dite`
  instructions.
- **PathHard's `stp` macro** no longer lists `astep, A` and only normalizes registers; its
  docstring says so. Each user step is `rw [astep_<kind> (show A a b f mode .l = _ from rfl)]; stp`,
  and the three call sites use `astep_call`.

**The caveat branches inside excluded declarations** are re-pointed where the edit is local:
- `arm_run`'s 16 `by simp [astep, hA]` side goals;
- `mrun_eq_arun`: `astep_ret hret`;
- `PSem.of_areach`: `astep_ret (NARM.detPart_choose hA false)`.

**What remains** (`evidence/round2/astep-residual.txt`; a grep of the head for `astep` in any
`simp`/`rw`/`unfold`/`delta`/`regs` list):
- the excluded machine comparisons: `ARMReach`'s `astep_cases` and `arm_step`, `MARM`'s
  `mstep_det`, `MARMCompile`'s `astep_mdetPart`, `NARM`'s `nastep_det`;
- two `rw [show (astep …)^[n] … = …]` statements in `PSem.of_areach`, which are statements about
  an iterate, not unfoldings;
- one docstring.

## Brief for the auditor

1. **Completeness:** does any proof outside `Machines/ARM` still unfold `astep`, in any form
   (including `simp` sets without `at`, `show`/`change`, macros and `decide`), other than the
   recorded exclusions? Are the exclusions really machine comparisons, whose subject is the step
   function itself?
2. **Scope:** is each change the old argument with the unfolding replaced by an equation? Are the
   `stp` macro's new body and its users consistent?
3. **Rule 10:** do the `show M .l = _ from rfl` instruction readings stay within each machine's
   own file? These read the file's own machine table, which is legal.

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/round2/freeze/`, 38 files, the head against the campaign's Lean
  `e4e7a419`): **no statement changes**, and no declaration added or removed in any file.
  182 bodies changed: 151 public and 31 private. These are the 6 named members (the five circuit
  equations and `astep_call₁`), the 173 in-scope declarations and the 3 caveat declarations.
- **Lint** (`evidence/round2/lint/`, `git archive`s of both trees). The campaign lint is identical
  at base and head:
  - `SpaceComplexity` 0 FAIL / 81 WARN / 112 files;
  - `CircuitComplexity` 0 / 76 / 104;
  - `ClassPSPACE` 0 / 10 / 14;
  - `Randomized` 0 / 51 / 65.

  The policy linter over the 38 files gives 17 findings at both, the same ones with shifted line
  counts: the existing file sizes, and the existing sketch gaps of `mult_contribution` and
  `mult_parity`.
- **Elaboration** (`evidence/round2/elab/`): every changed file, against the snapshot after #208,
  #212 and #213, gives exit 0, 0 errors and 0 warnings, the same as at the base. The `stp` macro's
  new body was also checked against `PathHardWalk` and `PathHardRun` with a renamed local copy.
  The base `PathHardRun` fails with that copy, as a negative control.
- **Replay** (`evidence/round2/merged-tree/`): `replay-las2` at `92e53e6e` covers the downstream
  closure of the 38 files, 109 modules, chained from the campaign snapshot after #216.
  **109 modules, 0 failed.** The static check finds 0 mismatches. The 21 `sorry` warnings are
  `ClassPSPACE/TQBF`'s existing ones. #217, #211, #218 and #219 merged afterwards:
  - none of the 38 files imports a module they changed in a way that matters (`TwoTapes`,
    `Hierarchy`, `Padding`);
  - #214 changes only proof bodies and one macro used only inside `PathHard*`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/105-as1-dedup/findings-r2.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `as1-dedup-r2-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
