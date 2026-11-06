## ===== campaign/gates/105-as1-dedup/pack-r3.md =====

# External audit pack, round 3: dedup AS-1 (PR #214, a dedup gate): the dispositions only

**Round 2** (`pack-r2.md`, `findings-r2.md`) was **HOLD: 0 blockers, 2 majors, 2 minors**. Both
majors widen the family beyond what #214 changes:
- **Finding 1:** implicit `astep` reductions by unification, with no `astep` in the text, such as
  `AReach.step` followed by `change`/`exact`. `Mult` crosses one fifth.
- **Finding 2:** consumers read each machine's instruction table (`A`, `CA`, …) across files, by
  `show A .l = _ from rfl` or `simp [A]`. That read predates AS-1.

**The user ruled on 2026-11-06: land #214 and acknowledge both majors as scoped debt, with
scheduled resolutions.** They are recorded as ledger families **AS-2** and **MT-1**
(`campaign/duplication-ledger.md`), each with its named members, its threshold crossing and its
resolution. Both are separate PRs in this dedup window, AS-2 after #214 merges. Minors 3 and 4
are accepted. The accounting conventions are reconciled, and the elaboration attestation is
narrowed to the retained logs (`resolutions.md`, § Round 2).

**#214's code is unchanged since round 2:** head `92e53e6e`, the same 38 files and the same
evidence.

## Brief for the auditor

1. **The acknowledgments:** do AS-2's and MT-1's ledger entries name round 2's members, the
   threshold crossing and a concrete resolution, as TEMPLATE requires for acknowledged debt?
2. **Minors 3 and 4:** are the reconciled site counts and the narrowed elaboration attestation
   accurate?
3. **#214:** confirm that the head is unchanged from round 2, so that round 2's notes 5–7 still
   stand.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/105-as1-dedup/findings-r3.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `as1-dedup-r3-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/105-as1-dedup/STATUS.md =====

# Gate 105 (#214, the dedup window's AS-1)

- 2026-11-06: the change `73629daf` (a sub-agent; the one member outside `CircuitComplexity`),
  #214 opened. `replay-las1` passed (7 modules, 0 failed, 0 `sorry`); freeze and lint in
  `evidence/`. Pack complete.
- 2026-11-06: staged (`outbox/gates/105-as1-dedup-gate/`, exchange commit `cb3039b2`): bundle
  `105-as1-dedup-bundle.md`, 17 sections, SHA-256
  `c80ff456bad64c7bd5776e930479a2e5c1b192d4d14bf205cd80267e144a456a`; Lean from `0bc71211`.
  Findings file `as1-dedup-findings.md`. **Ready to dispatch.**
- 2026-11-06: **dispatched** (the user).
- 2026-11-06: after dispatch, the user allowed colleague-owned edits; `1fd7d4ce` re-proves the five
  `BoolCircuit` members through the general equations (pushed to #214). Round 1 audits
  `0bc71211` as dispatched; the five go into round 2 with a new replay.
- 2026-11-06: round 2: #214 complete (`92e53e6e`); freeze, lint, replay-las2 (109/0); pack-r2 written; staged.
- 2026-11-06: round 2 **dispatched** by the user (140 sections, bundle `e935f140…`).
- 2026-11-06: round 2 findings: **HOLD 0/2/2** (implicit astep reductions; cross-file instruction-table reads). Awaiting the user's ruling.
- 2026-11-06: the user ruled: land, acknowledge both majors (AS-2, MT-1); round 3 (dispositions only) staged.

## ===== campaign/gates/105-as1-dedup/findings-r2.md =====

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `SpaceComplexity/Logspace/Mult.lean` · `mult_row_start`; `QueryReshape.lean` · `comp_factor_run`, `comp_valid_inner`; other consumers below | Round 1's completeness finding is not discharged. Concrete steps still reduce `astep` implicitly, including in declarations omitted from the census. | At head `92e53e6e`, `mult_row_start:746–750` applies `AReach.step`, then uses `change`/`exact` to compute the `.clearB` and `.clearDiagonal` steps without equations. `comp_factor_run:1579–1580` and `comp_valid_inner:2453–2454` similarly compute `.factorClear` and `.lookupReset`. These three declarations are absent from the 173-member list. The signatures of `AReach.step`/`AHalt.step` leave a premise starting at `astep`; matching the concrete continuation therefore unfolds it. Already-counted declarations also retain such reads: `Mult`'s `mult_contribution:636`, `mult_inner_loop:693–701`, `mult_outer_loop:821–829`, `mult_next_column:937–940`, `mult_columns_run:994–997`, `mult_last_bit:1139–1140`; `QueryReshape`'s `comp_multiply:1543–1544` and `comp_separator_run:2289–2290`. Adding `mult_row_start` alone raises `Mult` from 12/62 to 13/62 declarations, crossing one fifth; the severity guide therefore makes this major, not merely an accounting minor. | Re-point the remaining implicit computations to the instruction equations; extend the search beyond lines naming `astep`, including direct applications and unification. Regenerate the census and check consumers with a local irreducibility seal and controls, respecting the recorded structural exclusions. If debt is retained: **human acknowledgment required**, naming its scope and scheduled resolution. |
| 2 | major | `ClassPSPACE/TQBFARM/Leaf.lean:114`; `SpaceComplexity/Logspace/PathHardRun.lean:137`; `Codec/StepDecider.lean:72–79`; `Machines/NARMExample.lean:62` | The Rule 10 attestation is false: the new instruction readings do not stay in the machine's defining file. | `Leaf.lc_run` uses `show A (.lcF s) = _ from rfl`, but `A` is a `def` in `TQBFARM/Machine.lean:392`. PathHard's `A` is defined in `PathHardMachine.lean:387`. `StepDecider.pm_run` uses both `simp [CA, hm]` and `show … from rfl`, while `CA` is defined in `Codec/Machine.lean:320`. The same pattern occurs across TQBFARM, Codec, SavitchARM, PathHard, `LogspaceUniformAdj`, `CounterProgSimRun`, and `SpaceAmplifyPolyRun`. Even the same-file `guessValidA` example reduces imported `NARM.detPart`. These are ordinary definitions, not permitted reducible abbreviations. The retained dependence predates the rewrite, but the claimed compliance does not follow from wrapping it in `astep_*`. | Consume owner-side machine contracts or publish the necessary owner-side interface under the campaign policy; remove consumer-side definition reductions. Use existing `NARM.detPart_det` for deterministic-part readings. Sweep the whole replacement family. If retaining this cross-file debt: **human acknowledgment required**, with explicit scope and scheduled resolution. |
| 3 | minor | `campaign/items/dedup/as1-SCOPE.md`; `pack-r2.md`; `Machines/NARMPSem.lean` · `PSem.of_areach` | The site accounting and residual descriptions need correction. | The scope table sums to 583 sites, with 47 in its eight exclusions: 536 in-scope sites, not the pack's unexplained 501. Its search expressly omits unnamed definitional computations, explaining finding 1. Also, `Function.iterate_fixed rfl` at `NARMPSem:343,362,380` does compute `astep` at a halted configuration; the two displayed iterate statements are not evidence of “no unfolding.” These occurrences remain inside an already-recorded exclusion and do not independently enlarge the family. | Reconcile the counting conventions and regenerate the current ledger. Describe the halted-step reductions accurately; `arun_halted` already supplies the corresponding run fact. |
| 4 | minor | `evidence/round2/elab/`; `pack-r2.md` · elaboration attestation | The supplied local-elaboration evidence does not establish the entire stated check. | There are 35 changed-file logs, omitting `ARMProof`, `NARMKit`, and `UnaryLogspace`, plus two renamed-`stp` positive logs. They contain `exit=0`; no base negative-control log or reproducible control source accompanies the claimed `PathHardRun` failure. The separate 109-module replay covers all 38 changed files, so this is an evidence gap, not an observed compilation failure. | Supply the omitted local/base/control evidence, or narrow this attestation to the evidence actually retained. |
| 5 | note | Bundle, pinned trees, `evidence/round2/freeze/` | Integrity, change totals, and statement freeze verified. | SHA-256 is exactly `e935f140dcb39c8c1ec5066be091f91ef27b182c4f69aadf3c41d296f2665e79`. All 140 embedded sections match their designated Lean (`92e53e6e…`) or records (`91d3b529…`) Git blobs. The independently generated diff against `e4e7a419` matches the supplied diff: 38 Lean files, 725 additions, 567 deletions. Re-running the declaration comparison gives 182 changed bodies, 151 public/31 private, no statement changes or added/removed declarations: exactly the 173 listed consumers, six named equations, and three caveat declarations. Lean paths in this table are relative to `TCSlib/Complexity/`. | None for these checks; the verified freeze does not establish completeness or Rule 10 compliance. |
| 6 | note | Six named equations; `PathHardRegs.stp` and users; eight exclusions | The explicit equation replacements and macro change preserve the previous arguments; the exclusions are structurally justified. | `LogProg.astep_call₁`, AdjScan's three equations, and AdjWalk's two call equations now use the general equations and appropriate `vword_*` facts. The other explicit replacements preserve the instruction hypotheses and branch simplifications. `stp` removes `astep, A`; its users in `PathHardRun`/`PathHardWalk` perform the instruction rewrite first, including the three calls. The three caveat rewrites use the intended equations. Seven exclusions concern simulation/run comparisons; `astep_cases` is instead the general step-shape theorem, still appropriately structural. Findings 1–3 qualify the completeness and definition-reading claims. | None beyond findings 1–3. |
| 7 | note | `evidence/round2/lint/`, `merged-tree/`; later-merge dependencies | Lint and replay's static attestations verified; compilation success is supported by the supplied logs, not an independent Lean run. | Re-running lint reproduces base/head totals exactly: Space 0 FAIL/81 WARN/112 files; Circuit 0/76/104; PSPACE 0/10/14; Randomized 0/51/65. The same 17 policy findings remain after normalizing shifted locations. Independently reconstructed downstream closure and order match all 109 replay modules; all 38 blob pins match; the supplied log reports 0 failures/errors and 21 `sorry`s, all pre-existing TQBF occurrences, with 0 static mismatches. No affected dependency introduces the later `TwoTapes`, `Hierarchy`, or `Padding` changes; the relevant later NTIME/Loop/Nondeterministic changes preserve existing interfaces. Lean was unavailable here, so elaboration and negative-control execution were not independently rerun. | None for the reproduced static checks; preserve the distinction between verified source/log consistency and independently executed compilation. |

**Verdict: HOLD — 0 blockers, 2 majors, 2 minors.**

## ===== campaign/gates/105-as1-dedup/resolutions.md =====

# Gate 105 (#214, AS-1 dedup): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (SHA-256
`258b3096276701245123f51c7ed39e53f466d475f42beb55b560f1c01abad327`). **Verdict: HOLD: 0 blockers,
1 major, 0 minors, 4 notes.** The targeted rewrite of `astep_call₁` passes (note 2).

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Fixing in #214, all of it** (the user, 2026-11-06: "All 130 in #214"). A by-kind scope (`campaign/items/dedup/as1-SCOPE.md`) searched every closing form outside `Machines/ARM`: the `simp`/`simpa` family with `astep`, the `regs [astep, …]` macros, and PathHard's `stp` macro. It found **181 containing declarations in 40 files**. 8 are excluded as machine comparisons (`astep_cases`, `arm_step`, `arm_run`, `mstep_det`, `mrun_eq_arun`, `astep_mdetPart`, `nastep_det`, `PSem.of_areach`), with their literal one-step branches re-pointed where the edit is local. That leaves 173 in scope. Already on #214 (`1fd7d4ce`, `1856e771`, `5fdcfcf4`, `090fcccd`, `29c41e09`): the five circuit equations (now allowed: the user's 2026-11-06 ruling on colleague files), the auditor's four `TQBFARM` continuations (`rw [astep_call hl, vword_whole₁]`), `UnaryLogspace`'s `LtM.loop` and `ltLang_mem` (note 3), NARMKit's 17 and NARMPSem's 14 step lemmas, `AHalt.ret`/`MHalt.ret`, and four `QueryReshape`/`Mult` lemmas. The remaining 130 are in progress on the same branch. Round 2 audits the whole family on a fresh merged-tree replay. The ledger's AS-1 census is to be rewritten from the scope at round 2. |
| 2 | note | No change. |
| 3 | note | Included in finding 1 (`5fdcfcf4`). |
| 4 | note | **Superseded:** the five circuit members are re-proved through the general equations (`1fd7d4ce`), now that the user's ruling on colleague files allows it. |
| 5 | note | No change. |

## Round 2 findings (received 2026-11-06)

`findings-r2.md`, verbatim (SHA-256
`bce67db29cfcb29d32b77870324fa6458874fd237dd1c4b48a0ac118660b55a0`). **Verdict: HOLD: 0 blockers,
2 majors, 2 minors, 3 notes.** The freeze, the explicit replacements, the macro change and the
exclusions are verified (notes 5–7).

**The user's ruling (2026-11-06):** land #214 as it is, a strict improvement over the base, and
**acknowledge both majors as scoped debt with scheduled resolutions**, separate PRs in this dedup
window.

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Acknowledged (the user, 2026-11-06), ledger family AS-2.** These are implicit `astep` reductions by unification, with no `astep` in the text: `AReach.step`/`AHalt.step` followed by `change`/`exact` on a concrete continuation. The members named so far are `Mult`'s `mult_row_start`, `mult_contribution`, `mult_inner_loop`, `mult_outer_loop`, `mult_next_column`, `mult_columns_run` and `mult_last_bit`, and `QueryReshape`'s `comp_factor_run`, `comp_valid_inner`, `comp_multiply` and `comp_separator_run`. **Resolution:** a census by an `astep` irreducibility seal over every consumer, with controls, then a re-pointing PR, after #214 merges. `Mult`'s one-fifth crossing is part of the acknowledgment. |
| 2 | major | **Acknowledged (the user, 2026-11-06), ledger family MT-1, the machine-table equations.** Consumers read each machine's instruction table (`A`, `CA`, …, defined in `TQBFARM/Machine`, `PathHardMachine`, `Codec/Machine`, the SavitchARM, ExpBFS and circuit machine files) by `show A .l = _ from rfl` or `simp [A]`. That read predates AS-1: the old proofs did `simp [astep, A]`. #214 makes it visible; it does not create it. `NARMExample`'s `guessValidA` reduces `NARM.detPart` and should use `NARM.detPart_det`. **Resolution:** publish per-label instruction equations (`A_<label>`) in each machine's own file and re-point the consumers, a separate PR per machine directory in this window. Colleague files are mechanical, with an FYI. Round 2's pack wrongly said these readings stay within each machine's file. That claim is withdrawn. |
| 3 | minor | **Accepted.** The scope table counts unfolding occurrences per site at the base: 583 sites, 47 of them in the eight exclusions, so 536 in scope. The implementation report counts edited sites: 501, of which 18 are caveat sites. The two conventions differ because one edit can retire several occurrences on a line. The pack's 501 is the edit count. `PSem.of_areach`'s `Function.iterate_fixed rfl` (lines 343, 362, 380) does compute `astep` at a halted configuration. It is inside a recorded exclusion and is recorded under AS-2 (`arun_halted` gives the run fact). |
| 4 | minor | **Accepted; the attestation is narrowed.** The retained per-file logs cover 35 of the 38 files. `ARMProof`, `NARMKit` and `UnaryLogspace` are covered only by the 109-module replay, which elaborates all 38. The `stp` negative control's log was not retained, so that sentence is withdrawn. |
| 5–7 | note | No change. |

**Round 3** checks these dispositions and the ledger's AS-2 and MT-1 entries, with no change to
#214's code.

## ===== campaign/gates/105-as1-dedup/pack-r2.md =====

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

## ===== campaign/standards/TEMPLATE.md =====

# External audit pack — TEMPLATE

Copy this file to `audits/phaseN-pack.md`, fill every `⟨…⟩`, and hand the result (plus
the listed attachments) to an external LLM from a different vendor, in a fresh context
with no access to this repository's development history. Record the findings in
`audits/phaseN-findings.md`. A phase's findings must be addressed (fixed, or explicitly
waived with a reason) before the next phase begins.

---

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions, theorem
statements, and remaining `sorry`s. The proofs that exist are machine-checked — do not
review tactic scripts for correctness. The failure modes you are hunting are:

1. **Infidelity** — a definition that does not mean what the cited source means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons
   (vacuous hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Unprovability** — a `sorry`d statement that is false as stated, or whose stated
   form is subtly weaker/stronger than intended (boundary cases: empty input, `n = 0`,
   `k = 0` tapes, constant absorption).
4. **Missing hypotheses** — especially finiteness, positivity, and well-formedness side
   conditions the informal source leaves implicit.
5. **Debt** — wholesale duplication of existing proved material (private copies of
   another file's declarations, re-derivations of registry routines), even when
   disclosed and mechanically forced by file ownership. Report it at **major** with
   the proposed fix "human acknowledgment required": it does not block the gate on
   soundness, but the gate must not close without the human maintainer explicitly
   accepting the debt and naming its scheduled resolution. Screen for it
   cumulatively — verify the pack's duplication ledger (per-file copied-material
   totals) rather than assessing each copy in isolation.

   **Accounting inside an acknowledged family is a minor.** Once the human
   maintainer has acknowledged a debt family and named its resolution, a later
   correction to that family's *accounting* is reported at **minor**, not major.
   Examples are a missed member, a miscounted span, or an imprecise description of
   the screen. Such a correction does not change what was approved. It is a
   **major** again only if it changes the approval itself: the correction pushes a
   further file past the one-fifth threshold, reveals copies outside the
   acknowledged family's named scope, or shows the named resolution cannot work.

**Seals and reducible abbreviations.** A rule-10 seal (`attribute [local irreducible]` on
other-file definitions, each with an `rfl` control that closes unsealed and fails sealed) cannot
include a reducible `abbrev`: Lean's default reducibility validation refuses the attribute (the
unsafe override `allowUnsafeReducibility` is not used in seals). `policy.md` (*Definitions
land with their lemmas*) allows reading an abbreviation through its body, so that is not a finding.
Do report an `abbrev` passed to `simp`, `rw` or `unfold` where a published lemma exists, and a new
public `abbrev` without its lemma.

For **every definition** in scope: restate it in your own mathematical English *without
looking at the docstring first*, then compare your restatement against the cited source
location, and report any daylight. For **every `sorry`d theorem**: argue in 2-5 sentences
why it is true as literally stated, or exhibit the problem (ideally a concrete
counterexample or degenerate instance). Attempt at least ⟨3⟩ *adversarial
instantiations* — concrete pathological objects plugged into the definitions to check
they behave as the theory intends. Propose any machine-checkable sanity theorems you
believe are missing.

Do not give a blanket approval. Your deliverable is the findings table; an empty table
must be accompanied by the per-definition restatements that justify it.

## Scope

| Item | Where |
|---|---|
| Lean files under audit | ⟨list of files, with line ranges if partial⟩ |
| Source text | ⟨book/paper, edition, page/theorem numbers — auditor must have it at hand⟩ |
| Plan/context documents | `AroraBarakChapter1Plan.md`, `policy.md` §2-3 ⟨adjust⟩ |
| Out of scope | tactic proofs; vendored files' upstream design ⟨adjust⟩ |

## Known deviations (declared by the authors — verify they are benign, flag any others)

⟨Bulleted list: every deviation the docstrings declare, one line each.⟩

## Specific questions for this phase

⟨Numbered list of the doubts the authors actually have. Be concrete.⟩

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = statement is fixable but materially misleading as is, **or** accumulated
debt (failure mode 5) that the gate may not close over without explicit human
acknowledgment (accounting corrections inside an already-acknowledged family are
minors; see failure mode 5); **minor** = edge case or naming/attribution defect; **note** =
observation, no change required.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== workflow.md =====

# TCSlib Formalization Workflow

How large formalization campaigns are run in this repository. [`policy.md`](policy.md)
says what landed Lean code must look like; this document says what *process* produces
it. The reference implementation is the Arora-Barak campaign
(`AroraBarakChapter1Plan.md`, complete and audited end to end;
`AroraBarakChapter2Plan.md`, in progress) — file paths below cite its artifacts as
worked examples. Where an older document describes a mechanism this one supersedes
(e.g. the PR-based fill delivery in `AroraBarakChapter1Plan.md` §5, since replaced by
zip delivery), this document records current practice.

```
plan  →  statement phases  →  audit gates  →  fill campaign  →  closure
          (sorry-skeletons)    (per phase)     (epochs/batches)   (attestation, final
                                                                   audit, blueprint)
```

The load-bearing idea: **statements are audited before proofs are attempted.** Lean
already checks proofs; the dominant failure mode of formalization is a wrong or
subtly-weakened *statement*, and that is cheapest to catch while everything is still a
`sorry`. Every phase therefore lands as a compiling skeleton, passes an adversarial
external audit gate, and only then becomes fill work.

## 1. The campaign plan

Each campaign (typically one textbook chapter) begins with a plan file at the repo
root — `<Source>Chapter<N>Plan.md` — containing:

* **Scope**: which results are mandatory core, which are deferred, with source
  citations.
* **Foundation decisions**: the definitional conventions, each with its rationale
  (these are where audits bite; see §3).
* **Architecture and module layout**: directories, namespaces, facades, per policy §1.
* **Phasing**: the statement phases and the anticipated fill epochs.
* **Risks and honest effort assessment**.
* **Open design questions (human review required)**: decisions reserved for a human
  maintainer. Audit rounds *verify* these but never *dispose* of them; each records
  the maintainer's provisional choice and stays open until a human closes it. The
  consolidated register — full statements, cross-links, and status — is
  [`backlog.md`](backlog.md); the plans keep stable numbered stubs, which is what
  audit documents cite.
* **Decision log**: an append-only table. Every methodological decision, every audit
  round's verdict, and every repair round gets a row. The log is the campaign's
  memory; when a decision is reversed, the old row is marked **Superseded** in place,
  never deleted.

## 2. Statement phases (sorry-skeletons)

A phase lands the definitions plus the theorem *statements* of one coherent slice,
every proof a `sorry` under a policy-grade proof sketch (policy §3: the sketch is
written at skeleton time and is the plan; a skeleton whose sketch cannot be written is
not ready to land). Ground rules:

* Definitions and sorried statements only. Proofs appear in a skeleton only for
  definitional-unfolding lemmas whose home module mirrors proved infrastructure (the
  precedent: the `runWith` algebra of `TuringMachine/Nondeterministic.lean`, mirroring
  the vendored `runFrom` lemmas), and any such deviation is flagged in the audit pack
  with the proofs declared part of the audited surface.
* Sketches name their obligations: a sketch that will need a machine construction
  names each sub-machine as an explicit fill obligation, so the eventual brief can
  inherit the list. It also names every **host** the route needs (policy §1, **Hosts come
  first**), from the registry in `machine-library-design.md` §14. A sketch that needs an
  unregistered host is not ready: the host's public contract is a statement-phase item of
  its own, gated before the consumer's fill.
* Everything gate-verifies before commit: per-module checks plus a full fresh sweep
  (§6), style lint, and the headline axiom prints.

## 3. Audit gates (between phases)

Right after a skeleton lands — statements frozen — an **external adversarial audit**
runs before any fill or any next phase. The auditor is an LLM from a different vendor,
in a fresh context, reviewing the trusted surface (definitions, statements, sketches,
and any skeleton-time proofs) against the source text.

**Artifacts**, committed under `audits/` with campaign-scoped names
(`ch2-phase1-*`, `epoch4-*`), except the bundle:

* `…-pack.md` — the auditor's instructions: the audited commit, repository-side
  attestations (freeze by path enumeration, sweep results, admission inventory, axiom
  prints, lint — stated so the auditor can verify or challenge them, with source facts
  kept separate from maintainer execution claims), the under-audit inventory, a
  prioritized brief (the plan's seeded design questions go here), and the findings
  table format with the severity guide: **blocker** (a downstream phase would build on
  a wrong statement) / **major** (fixable but materially misleading) / **minor** /
  **note**. `campaign/standards/TEMPLATE.md` is the skeleton.
* `…-bundle.md` — a single uploadable file: the pack verbatim, then every attachment
  under a `## ===== <path> =====` header (prior findings, both plans, `policy.md`,
  the root, and the full module tree). **Not committed** (user, 2026-10-15): it is kept
  in the local dispatch folder, and the resolutions record its SHA-256 and section
  count. Bundles committed before then are indexed in `campaign/BUNDLES.md`, with how to
  retrieve them from history.
* A short kickoff message (drafted per round, pasted by the maintainer into a fresh
  auditor chat with the bundle attached).
* `…-findings.md` — the auditor's report, preserved **verbatim**, including anything
  the maintainer disputes. Pack errata found later are acknowledged in the resolutions
  file; shipped packs are never edited retroactively.

**The gate rule**: a gate closes only on a round reporting **zero blockers and zero
majors**. A round with majors triggers repairs and a full re-audit round (minors may
be swept in the closing commit and re-verified). Repairs adopt the auditor's own
constructions where supplied, are re-gated, and are recorded in the decision log; when
the loop closes, `…-resolutions.md` summarizes every round, every repair, and the note
dispositions. The complete worked example is the three-round
`campaign/gates/ch2-phase1{,-reaudit,-round3}/{pack,findings,resolutions}.md` loop.

Audits complement, never replace, in-Lean sanity theorems — the machine-checked and
permanent form of the same checks.

## 4. The fill campaign (epochs and batches)

With all phase gates closed, the audited-true sorries are filled in **epochs** —
sequential, ordered by risk retirement, with an audit round at each epoch boundary —
each consisting of **batches** run in parallel by cloud agents with disjoint file
ownership, from self-contained briefs in `briefs/`.

**Binding batch ground rules** (full text repeated in every brief):

1. **Exclusive file ownership.** Helpers live `private` in owned files; a lemma that
   belongs in a shared file is *requested* in the report and added serially at epoch
   merge, flagged for the next audit. **Hosts are the exception** (rule 4).
2. **Statement freeze.** Audited declarations are never renamed, re-signatured, or
   re-stated by fill work. A target that looks unprovable as stated is an
   *escalation*, reported with the obstruction — never "fixed" inline.
3. **Verification per batch**: the check script (§6) over the owned files, zero
   `error:` lines, sorries only at documented out-of-scope items.
4. **Hosts first** (user, 2026-10-12; policy §1). A batch never builds a search,
   recursion, interpreter, runner or input device as a private one-off. It cites the
   registered public host its brief names. If the route turns out to need a host the
   brief does not name, that is an escalation, reported with the contract the batch
   would need; the batch continues on its other targets.

**Hosts in briefs.** A fill brief is issued only when every host its route needs is
registered (`machine-library-design.md` §14) and the host's statement gate has closed. The
host's own fill may run in the same wave, in its own batch, with consumers citing it under
the proved-modulo rule. The readiness check for any target lists the hosts it needs. A
private host already in the tree is harvested (a promotion PR and its gate) before a second
consumer is briefed against it.

**Delivery is by zip, not PR.** Each batch returns an archive containing `REPORT.md`,
the full source files, a `git format-patch` series, a git bundle, the batch's sweep
log, the axiom-print log, and `SHA256SUMS`. The maintainer verifies before
integrating: checksums; the statement freeze (comment-stripped comparison of every
audited signature); enumeration of any removals; public-declaration drift; a full
fresh sweep; the headline axiom prints; and the **duplication ledger** — every
private copy of existing proved material in the delivery enumerated, with each
touched file's cumulative copied-material count and fraction. If a delivery pushes a
file past **one fifth copied material**, or adds copies to a file that already
received copies in an earlier epoch, the maintainer opens a `backlog.md` §1
human-review item before the epoch's audit pack ships — no discretion. Integration
is `git am -3` from the patch series, preserving the agent's authorship. Large fills that exhaust one agent's budget
continue via a continuation brief to a fresh agent (the `universal` B2 precedent).

**Counting public names** (user, 2026-10-22; gate 59). Public-declaration drift, the statement
freeze and a brief's "no new public declaration" rule count **public declarations**: the
declarations the source introduces without `private` (`theorem`, `lemma`, `def`, `abbrev`,
`instance`, `structure`, `inductive`, `class`), counted by the comment-aware source census
(`devtools/seyoon/declfreeze.py`). Packs say so ("N → N public declarations, at source"). A
**public constant** is a non-private name in the module's elaborated environment (the axiom
probe's walk of the module's publics). Packs and reviews report a module's new public constants
separately, by kind:
- a declaration's compiler auxiliaries (`_proof_N`, `_simp_N`, `match_N`, `eq_N`, `eq_def`,
  `congr_simp`);
- the instances that `deriving` generates for a **private** type, which Lean 4.25 names publicly
  (e.g. `instDecidableEqSl_Key`).

Neither kind is a public declaration. A derived instance of a private type needs no finding when
its type is private to its file and a name check over the tree and the open PRs finds no clash;
where a derived name would clash, write an explicit `private instance`. Any other new public
constant is reported as a finding.

**Epoch boundaries**: the maintainer re-runs the full sweep, produces a **drift
attestation** (§6), and prepares the epoch's audit pack with elaboration evidence
and the epoch's **duplication ledger**, which the auditor verifies independently
(audit template failure mode 5); the epoch's gate follows the same
zero-blockers/majors rule as phase gates, and a debt major closes only by explicit
human acknowledgment recorded in the resolutions file. Once a family is
acknowledged, later corrections to its accounting are minors (audit template
failure mode 5) and do not hold the gate; the ledger is still corrected.

## 5. Closure

When the last sorry falls: a zero-sorry sweep with build evidence; a campaign-wide
drift attestation against the audited baselines; a final audit pack covering the fill
rounds; and the blueprint increment — dependency graph from `.ilean` artifacts,
`scripts/blueprint_{enumerate,assemble,validate}.py`, blueprint-writer agents, with
the blueprint **late-bound** throughout (extraction only at boundaries; no blueprint
LaTeX hand-written ahead of the Lean; `blueprint/BLUEPRINT_PIPELINE.md` has the
pipeline detail).

## 6. Verification tooling

* **`scripts/lean_check_tree.sh <module>`** — the campaign's elaboration gate: a
  direct `lean` invocation per module (**`lake build` is banned on campaign
  branches** — see the Chapter-1 decision log), emitting fresh `.olean`s into a
  scratch tree. Pass requires exit 0, zero `error:` lines, *and* a fresh olean, so a
  stale artifact can never satisfy the check. The full sweep runs it over every
  module, in dependency order, from `scripts/ab_ch1_module_order.txt`:

  ```
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < scripts/ab_ch1_module_order.txt )
  ```

  Admission counting is by `declaration uses 'sorry'` warnings in the sweep log; the
  expected count is attested in every pack.
* **`scripts/campaign_style_lint.py`** (named `scripts/style_lint.py` until the
  main merge, which adopted main's per-file policy linter under that name — the
  historical audit logs' invocations refer to this tool) — mechanical policy checks: statement-prose docstrings,
  sketch-before-sorry, file sizes, `## References`, facade coverage, and (check 8, since
  2026-10-16) public definitions without a lemma beside them (`policy.md` §1, *Definitions
  land with their lemmas*). Campaign baseline: zero FAIL (legacy pre-campaign files outside
  the audited surface are tolerated and listed). Check 8 is a WARN listing names; a landing
  adds no name to it.
* **Axiom prints** — `#print axioms` for every headline theorem on the *fresh* olean
  tree: closed results must show exactly `[propext, Classical.choice, Quot.sound]`;
  sorried statements show `sorryAx`, and any other axiom is a stop-the-line event.
* **Drift attestation** — the anti-tamper check between audited baselines: strip
  comments from every module, compare both the **multiset** of declarations and the
  **ordered declaration sequence** against the baseline, and enumerate public
  declarations (gained / lost / changed) so that "nothing audited moved" is a checked
  claim, not an impression.
* **Vendored files** are frozen at their recorded upstream pin and periodically
  byte-compared against upstream; local modifications live only in the header list.

## 7. Relationship to the other documents

* [`ROADMAP.md`](ROADMAP.md) — a one-page orientation: the phases ahead and pointers to
  the documents that hold the detail.
* [`policy.md`](policy.md) — the standards this workflow enforces (modularity,
  attribution, sketches, review checklist).
* [`lean-glossary.md`](lean-glossary.md) — the Lean/Mathlib jargon appearing in
  declaration names and docstrings (fuel, Sigma, `Prop` vs `Bool`, the naming
  grammar, …), for readers fluent in TCS but not in Lean.
* [`AGENTS.md`](AGENTS.md) / `.claude/` — the sorry-ladder proof technique and agent
  roster; useful *inside* a fill batch, but campaign verification runs through §6, not
  through `lake build` or editor-only checks.
* [`blueprint/BLUEPRINT_PIPELINE.md`](blueprint/BLUEPRINT_PIPELINE.md) — blueprint
  generation and validation.
* [`.github/copilot-instructions.md`](.github/copilot-instructions.md) — main-branch
  build and CI; campaign branches deviate as recorded in their decision logs.

## ===== campaign/duplication-ledger.md =====

# Cumulative duplication ledger

The standing per-file accounting of copied proved material that
`workflow.md` §4 requires at every epoch boundary. Created as the
retrofit-R1 round-1 repair (R1-2); **rebuilt at round 2** (R2-1/R2-2 of
`audits/retrofit-r1-r2-findings.md`): the first version's arithmetic was
inconsistent (summands 261 against a printed 249), its inclusion rule was
applied asymmetrically, and it **misclassified an exact three-file copy
family as "design-harvest reimplementation"** — the round-2 auditor
proved the four relocation declarations byte-identical across `Loop`,
`Primitives`, and `Hardness` after consistent identifier substitution,
and found the 13 exact Loop-internal H3 copies omitted. This version
adopts one inclusion rule, enumerates every family, and uses the
auditor's independently computed figures wherever they exist.

## Counting convention (one rule)

**Primary rule — expanded correspondence membership**: a declaration is a
ledger member iff it belongs to a *recorded cross-declaration
correspondence* — the retrofit inventories' twin maps **including their
strengthened-counterpart rows**, the A2/F2A reports' declared copies, and
the round-2 audit's verified relocation and H3 families. Each member is
counted **once per file it inhabits**. (Secondary, where it differs: the
*strict normalized-byte-twin* count excludes the five strengthened
counterparts — Loop's `loopHost_prepare`/`loopHost_contracts`,
Primitives' `splitSolve_of_body`/`_source`/`_closed` — and H3's one
near-copy `_init` pair.) Fractions are members over the file's total
declarations. Line figures use the round-2 audit's span rule — attached
docstring and intervening closure note through the last code line,
excluding separating blank/module-note blocks — with the auditor's
computed values where available and estimates under the same rule marked
`≈`.

## State after retrofit epoch R1 (the merged PRs #9/#10)

| File | Total decls | Original-side members | Copy-side members | All members | Fraction | Lines in member blocks |
|---|---:|---:|---:|---:|---:|---:|
| `Build/Loop.lean` | 212 | 87 →Catalog (of the historical 95; strict 85) + 4 relocation originals (`emCallAction`/`emCallCfg`/`emCall_apply`/`emCall_relocate_run`, the batch-L source of the three-file family) | 13 H3 exact copies (`emLoopHost_*`; their `loopHost_*` originals are already in the 87 and are not double-counted; the `_init` and `_anchor_return` near-copies are counted as source-side members since round 7 — Catalog twins reproduce them cross-file) | **98** after RB4 (merged, PR #13 `b2833d46`; was 117 — generated, pass 4): 88 historical + 10 from pairs. RB4 deleted 12 H3 copies, the 4 relocation originals and `emLoopHost_init`; `emLoopHost_anchor_return` and `emLoopHost_start` no longer reproduce a Catalog proof after the agreement-transfer rewrite | **49.2%** (98/199) | **2,647** (was 3,153; both totals from the script's span routine, which reproduces the audited 3,153) |
| `Build/Primitives.lean` | 259 (272 before RB5) | 146 →Catalog (of the historical 150; strict 143) + **6 public originals** reproduced in Catalog (round-5 screen: `computesFunInTime_stripLast` → the adaptation `f2_strip_linear`; `_prepend`, `_pairEncodeFixed`, `_pairFst`, `_pairSnd`, `_pairConcat` → their strengthened `_spaceUsed` counterparts) | **none** — RB5 (PR #14, merged 2026-10-10) deleted the 4 relocation copies (`emitterP2Action`/`emitterP2Cfg`/`emitterP2_apply`/`emitterP2_relocate_run`, formerly byte-identical to Loop's) | **168** after RB5 (was 173) — generated (pass 4): 145 historical (the 4 relocation members and the `splitEmbed_run` twin are deleted) + the same 23 sources of like-kind MEMBER pairs (the 6 round-5 publics, round-6 `emitterP2_control`, and 16 found by the complete round-7 pass: `emitterAppend_run`, `emitterP2EraseTM`, `emitterP2StateDecidableEq`, `emitterP2_erase_scan`, `emitterP2_prepare_rewind_candidate`/`_suffix`, `emitterSplit_find`/`_loop_bound`/`_of_body`/`_result`, `emitterTokenTM`, `emitterToken_double`/`_separator`, `emitter_first_entry`, `mapCfg`, `mapStart`) | **64.9%** (was 63.6%) | **3,790** before RB5 (3,415 + 375 round 7); not re-measured after it |
| `CookLevin/Hardness.lean` | 545 (549 before RB5) | 0 | **none** — RB5 deleted the 4 relocation copies (`clSlotAction`/`clSlotCfg`/`clSlot_apply`/`clSlot_run`) and `clMap_run`. Not copy debt, but recorded: its replacement certified-layout layer `clPlacement` is a private generic adapter, scheduled for dissolution as 12.2c item 13 | **0** (was 4) | **0%** | 0 (was 73) |
| `Build/Catalog.lean` | 428 (423 at the R1 close, plus the five §12.6 framed contracts) | 2 in-file originals (`f2_finSumEquiv`, `f2_sum_add` — their `a2_` copies are normalized-identical, round-3 verified) | 150 Primitives-sourced + 95 Loop-sourced + 17 Wrappers-sourced (10 `f2_timed*`, 7 `catalog_redirect*`) + 2 in-file `a2_` copies + **3 Composition-sourced** (`f2_idTM`, `f2_idTM_run`, `f2_constTM` — maintainer-reconciled normalized-identical to `Composition.lean`'s originals) + **20 counter-block members** (`f2_counterInc` … `f2_counter_computes` — maintainer reconciliation, declaration by declaration: **19 normalized-identical** to `ClassP/TimeConstructible.lean`'s originals, and `f2_counter_computes` a **near-copy adaptation** of the proof body of the public `timeConstructible_id`) + **7 strengthened public counterparts** whose time conjuncts reproduce a public source proof (`computesFunInTime_id_spaceUsed`/`_const_spaceUsed` ← `Composition.lean`, round 4; `_prepend`/`_pairEncodeFixed`/`_pairFst`/`_pairSnd`/`_pairConcat_spaceUsed` ← `Build/Primitives.lean`, round 5 — 89-100% of each source proof reproduced) + **2 F2A adaptations** of public proofs (`f2_strip_linear` ← `computesFunInTime_stripLast`, 86% of the source reproduced — round-5 finding R5-1; `f2_counter_heads` ← `timeConstructible_id`, 64% — round-5 screen) + **20 round-6 members** from the exhaustive screen: R6-1's `f2_counter_count_space` (80.3% of the private `counter_count`) and 19 further cross-file adaptations — 4 F2A (`f2_exists_loopFind_space` 97.8% of `exists_loopFindTM`, `f2_cond_time` 92.0% of Wrappers' `computesFunInTime_cond`, `f2_rewind_heads` 90.8% of `catalogRewind`, `f2_cond_ledger` 70.3% of `timed_start`), 13 A2 (`a2_map_block`/`_suffix`/`_backA`/`_backB`/`_parse`/`_setup`, `a2_mapVirtual_run`, `a2_mapSetup_stationary`/`_run`/`_heads`, `a2_call_run`, `a2_loop_prepare` 86.8% of `loopHost_prepare`, `a2_loop_round`), and 2 public rows (`computesFunInTime_pairLenCheck_spaceUsed` 71.4% of `computesFunInTime_pairFst`; `exists_loopTM_spaceUsed` 85.5% of `exists_loopCfgTM`, 81.0% of `exists_loopTM`) | **318** | **74.3%** (75.2% of 423 at the R1 close; strict — excluding the 34 strengthened counterparts/adaptations and the 1 near-copy: **283, 66.1%**) | **7,539** (6,267 round-4 measured + 224 round 5 + 52 R6-1 + 996 for the 19) |
| `Build/Wrappers.lean` | 29 (10 pub + 19 priv) | 17 + 1 round-6 source (the public `computesFunInTime_cond`) | 0 | **19** — generated (pass 4): 17 historical + `computesFunInTime_cond` (round 6) + `captureCfg` (round 7) | **65.5%** | **355** (297 + 40 + 18) |
| `ClassP/TimeConstructible.lean` | 21 | 20 (the 19 identical counter originals + `timeConstructible_id`, the source of both the near-copy `f2_counter_computes` and the adaptation `f2_counter_heads`; the private `counter_count` is likewise the source of R6-1's `f2_counter_count_space`) | 0 | **20** | **95.2%** (strict: 19, 90.5%) | 355 (round-4 measured) |
| `TuringMachine/Composition.lean` | 19 | 5 (`idTM`, `idTM_run`, `constTM` + the public `computesFunInTime_id`, `computesFunInTime_const` whose proofs the Catalog rows reproduce) | 0 | **6** — generated (pass 4): + `controlCfg_run` (R7-1) | **31.6%** (strict: 3, 15.8%) | **109** (97 + 12) |
| `Build/Embed.lean`, `Build/Seam.lean`, `Build/VirtualInput.lean`, `Build/Zone.lean`, `Simulation.lean` | — | 0 | 0 | 0 | 0% | 0 |
| `Codes2Tape.lean` (ZF-B/B2/B3, integrated 2026-10-10) | 49 (9 pub + 40 priv; B3 added 16 new, non-copy privates) | 0 | **23 format-specific adaptations** of `CodeParser.lean`'s / `MathlibBridge.lean`'s one-tape top layer (20 retargeted + `zfBParse_full`/`zfBCanonical`/`zfBCanonical_eq`; agent-measured 60–100% body share) — the 46 format-independent copies were deleted after the promotion (f171767f) | **23** | **46.9%** (strict 3, 6.1%) | 290 code lines (agent-measured) — over one fifth: `backlog.md` §1 CH34-D2, **ACKNOWLEDGED (user, 2026-10-10) → 12.2c tasklist item 8** |
| `Robustness/SingleTape.lean` (ZF-C2) | 100 | 0 | 0 — **3 in-file near-duplicates noted, uncounted** per the in-file convention (maintainer screen: `dgPos_move` 93.1% of `sweepPos_move`, `dgStart` 72.9% of `sweepStart`, `dgInput_read` 64.3% of `sweepInput_read`; the agent disclosed the first and third as borderline) | 0 | 0% | 0 |

**Reconciliation notes (rounds 3-4 repairs)**: the F2A report's 306
inventory entries decompose as **150 Primitives + 94 Loop + 10 Wrappers +
3 Composition copies + 20 counter members + 2 in-file originals + 7
adaptations (`f2_strip_linear`, `f2_counter_heads`, round 5;
`f2_counter_count_space`, `f2_exists_loopFind_space`, `f2_cond_time`,
`f2_rewind_heads`, `f2_cond_ledger`, round 6) + 20 nonmembers** (the
round-4 correction: the old "29 outside" wrongly included the two counted
in-file originals); the 20 share no member-level material with any
declaration of the five source files (round-6 exhaustive screen below) (the `f2_polyHeads`/`f2_space_of_time`/
`f2_segment_heads`-class engines and strengthenings — round-4 sampled and
accepted). The A2 report's 45 declarations contribute 2 in-file copies +
`a2_loop_halted_run` (in the Loop 95) + **13 cross-file adaptations**
(round-6 screen) + 29 new constructions. Catalog's union:
`318 = 286 F2A + 16 A2 + 7 earlier redirect + 9 public counterparts`.

**The public-proof screen (round-5 repair of R4-1; R5-1/R5-2/R5-3).**
Published as `audits/evidence/retrofit/r1-public-proof-screen.py` with its
output `r1-public-proof-screen.out`. *Erratum:* the round-4 run tested
whether a source proof was contained **whole** in its counterpart, but the
round-4 text described "segments ≥ 60 characters". The round-5 auditor ran
the method as described and found six fragment hits that the containment
test could not see. The method below is the one actually run.

- **Method.** Strip comments and all whitespace. Rename each source
  identifier `h` to `f2_h` wherever Catalog declares `f2_h` (dotted names
  split). Report two measures:
  - the **longest common contiguous segment** (LCS), with the literal ≥ 60
    candidate threshold;
  - the **shared length**: greedy string tiling with blocks of at least 25
    characters, as a fraction of the **source** proof.
- **Rule.** A pair is a **member** when at least half of the source proof
  reappears in the target, with an absolute floor of 60 shared characters
  so that a one-line citation of a public lemma counts as reuse. Any other
  shared tiling of at least 60 characters is a recorded **fragment**, not
  counted. The rest are citations or no match.
- **Population (R5-3).** 17 eligible pairs: 2 from Composition (`id`,
  `const`) and **15** from Primitives, not the 16 stated in round 4. Five
  source theorems have no `_spaceUsed` counterpart: `ifEq`, `comp`,
  `splitSolveWith`, `unaryToken`, `appendBit`.
- **Pass 1, direct pairs.**
  - Members (7): `id` 96.5%, `const` 97.1%, `prepend` 93.9%,
    `pairEncodeFixed` 100%, `pairFst`/`pairSnd` 88.8%, `pairConcat`
    88.7%.
  - Fragments, recorded and not counted (3): `polyUnary` (119 characters
    shared, 46.7%); `pairLenCheck` (305, 21.9%; its LCS is the 91-character
    `Nat.pow_one` bound); `stripLast` (221, 11.7%; its LCS is the
    121-character `have hn` weakening).
  - Citations or no match (7): `lengthBits`, `polyBits`, `pairValid`,
    `pairDup`, `pairMapSnd`, `splitSolve` (the auditor's 27-character
    citation), `incFixed`.
  - The literal ≥ 60 LCS screen reproduces the auditor's hit set exactly
    (`id` 776, `const` 273, and 62/75/75/75/91/121 for the six Primitives
    pairs). One member falls below the 60-character LCS threshold:
    `pairEncodeFixed`, whose longest block is 53 characters but whose whole
    91-character source proof reappears. This is why the rule measures
    coverage, not contiguity alone.
- **Pass 2, residual helpers.** Each of the 27 nonmembers recorded in
  round 4 is screened against every public proof of Composition,
  Primitives and TimeConstructible, taking the best match by shared length.
  - Members (2): `f2_strip_linear` (86.0% of `computesFunInTime_stripLast`;
    R5-1) and `f2_counter_heads` (64.1% of `timeConstructible_id`; the
    auditor's 215-character partial-reuse candidate, which crosses the
    member bar once measured by tiling).
  - Fragments, recorded (6): `f2_counter_count_space` 6.5%,
    `f2_unary_sharp` 35.7%, `f2_cond_time` 30.0% (vs
    `bufferedCompTM_computesInTime`, a candidate the auditor did not list),
    `f2_rewind_scan_heads` 7.4%, `f2_rewind_heads` 6.0%,
    `f2_cond_ledger` 11.7%.
  - The remaining 19 share under 60 characters with any public proof.
- **Round-6 repair (R6-1, R6-5): pass 3, exhaustive.** Round 6 found
  R6-1, which the public-only residual pass could not see. Pass 3 replaces
  that scope limit. **Every one of Catalog's 124 non-members** (all of
  Catalog minus the post-R6-1 299-member union, computed by name in the
  script) is screened against **every declaration, public and private, of
  Composition, Primitives, TimeConstructible, Loop and Wrappers** (553
  declarations, of which 542 have an extracted body of at least 25
  characters; the other 11 cannot reach the 60-character floor). An exact 25-character prefilter is used; it loses nothing,
  because every tile is at least 25 characters. Verdicts compare like with
  like, proof with proof and term with term, so a proof that spells out a
  definition's term is reported as a restatement and not counted. **Every**
  qualifying pair is printed, not just each target's best match (R6-5).
  - Result: **19 cross-file members**, all counted in the Catalog row
    above. *Round-7 correction:* the round-6 text derived the source side
    from each target's best match only, giving "6 new source-side members"
    (R7-1). Pass 4 below replaces that hand step.
  - Five A2 members reproduce just over half of one 129-character Loop
    proof, `emLoop_run_prefix`. They are counted, as the rule requires,
    and flagged as low-coverage.
- **Round-7 repair (R7-1, R7-2): pass 4 generates the census.** No
  per-file member count is assembled by hand any more. **Pass 4** runs the
  like-kind rule over **all 423 Catalog declarations**, not only the
  non-members, against all five source files: 537 like-kind MEMBER pairs.
  **Every** pair's source joins its file's member set, together with the
  historical rules, stated by name in the script: f2_-twins, the
  `a2_loop_halted_run` twin, the relocation family, the 13 H3 copies, the
  counter block and `catalog_` twins. The script prints each file's count
  and every member beyond the historical rules, with spans. The rows above
  quote it.
  - Pass 4 reproduces the auditor's R7-1 additions (`controlCfg_run`,
    `emCall_right_run`, `exists_emitLoopTM`).
  - It also finds **24 further source-side members** (Primitives 16, Loop
    7, Wrappers 1). These are source declarations that a Catalog twin of a
    *sibling* declaration reproduces by more than half, so their material
    is duplicated in Catalog. Two of them are Loop's H3 near-copies
    `emLoopHost_init` and `emLoopHost_anchor_return`, previously
    "noted, uncounted"; they are now counted through the cross-file path.
  - Catalog is unchanged at 318.
  - **R7-2:** the body extractor now handles equation-style definitions and
    inductives (text from the first depth-0 `|` or `where`). The population
    labels are exact: 553 source declarations, 542 with an extracted body
    of at least 25 characters; the other 11 are genuinely shorter. Pass 3b
    carries the kind guard: **107 like-kind in-file pairs over 62 targets
    (12 at 90% or more), plus 2 restatements** (`f2_cond_ledger` ~
    `f2_timedReadyCfg`, `a2_loop_prepare` ~ `f2_loopReady`).
- **The membership rule in one sentence.** A declaration is a member when
  it is a historical twin or copy, or when it is either side of a
  like-kind cross-file pair in which at least half of the source's
  extracted body, and at least 60 characters, reappears in the target. The
  **exception** is in-file near-duplicates, which are recorded (pass 3b)
  and not counted; in-file exact copies are counted.
- **Standing in-file convention, stated explicitly.** Pass 3b lists
  in-file near-duplicates among the non-members: **109 raw printed
  pairs, of which 107 are like-kind, over 62 targets**. Twelve like-kind
  pairs reach 90%, and the other 2 are kind-mismatched restatements. They
  are led by the §12 sibling
  machine rows (`transferTM` against `copyTM` 99.8%, and the
  clear/compare/increment rows), which are public constructions audited at
  the §12 and F1 gates. Per the ledger's standing convention, which counts
  in-file **exact** copies (the H3 thirteen, the `a2_mapSumEquiv`/
  `a2_map_sum` pair) and **notes in-file near-duplicates without counting
  them**, they are recorded, not counted. None is an exact copy. Their
  disposition is the 12.2c per-theme split, which factors these families.
  An in-file near-match alone never adds a member. A declaration can still
  be a member independently through a cross-file pair: Loop's
  `emLoopHost_init` and `emLoopHost_anchor_return` count because their
  Catalog twins reproduce them.
- **Coverage qualification.** The screen covers the five source files of
  Catalog's copy families, in full, at the stated thresholds. Copies from
  files outside those families, or adaptations restructured below the
  25-character tile size, are outside it.

Copy-side counts deliberately include copies whose originals were deleted
in R1 (the copies persist; deletion of an original does not shrink the
copy side). The Loop inventory's recorded dispositions — the 8 dead
Loop-twin copies in Catalog (`f2_loop_silent_prefix`,
`f2_loopBody_capture`, the six `f2_loopDebit*`/`f2_loopBorrow*`) and the
orphans' dead twins — are **dispositions for 12.2c, not subtractions
here**; sole-owner/dead labels require Catalog's reference graph and are
settled at that window. Internal near-duplicates flagged by the
inventories but outside the rule (`clCountTape ≡ bufferTape`) are noted,
uncounted. The H3 `_init` pair, once in this list, counts since round 7
through its cross-file Catalog correspondence.

**Epoch R1 delta**: new copies **0**; the historical maps lost **eleven
dead originals plus one live original eliminated by replacement**
(`catalogPair_inverse`, the human-approved E1) — 245 → 233 surviving
→Catalog originals (R2-3 wording); net −1,639 lines, −83 private
declarations (76 dead + 7 replaced).

## Epoch 2, B1 (PR #26): the oracle layer and FH-1

Added at the B1 fill-gate close (`audits/b1-fill-findings.md`, finding 2).
The primary rule applies: each member is counted once per file it
inhabits, and fractions are over the file's total declarations at
`integrate/b1-oracle`. None of these files had a ledger row before.

| File | Total decls | Original-side members | Copy-side members | All members | Fraction | Disposition |
|---|---:|---|---|---:|---:|---|
| `TuringMachine/Oracle.lean` | 42 | 0 | 2: `OracleTM.runFrom_comm_of_step` (63/63 both ways against Deterministic's) and `OracleTM.ComputesInTime.output_unique` (72/87 = 83% of Finite's) | **2** | **4.8%** | Approved forced mirrors (B1 decision 6; gate note 16) |
| `TuringMachine/Deterministic.lean` | 34 | 1: `MultiTapeTM.runFrom_comm_of_step` | 0 | **1** | **2.9%** | Mirror source |
| `TuringMachine/Finite.lean` | 18 | 2: `FinTM.ComputesInTime.output_unique` (mirror source) and `MultiTapeTM.exists_first_halt` (FH-1's public form) | 0 | **2** | **11.1%** | Sources |
| `ClassNP/EXP.lean` | 153 | 0 | 1 (FH-1): `enumCont_first_halt` | **1** | **0.7%** | FH-1, to retire (`backlog.md`) |
| `ClassNP/SAT.lean` | 282 | 0 | 2 (FH-1): `sat_first_halt`, `sat_call_first_halt` | **2** | **0.7%** | FH-1 |
| `CookLevin/Hardness.lean` | 545 | 0 | 1 (FH-1): `clA5_call_first_halt` | **1** (was 0) | **0.2%** | FH-1 |
| `Build/Catalog.lean`, `Build/Loop.lean` | 428, 194 | — | FH-1: `f2_loop_first_halt`, `f2_splitCount_firstHalt` (Catalog); `loop_first_halt` (Loop) | unchanged | — | `loop_first_halt` and `f2_loop_first_halt` are a 341/341 twin pair, already counted in the Loop→Catalog family. `f2_splitCount_firstHalt` is in the F2A-22 inventory; whether it is one of Catalog's 318 members or one of the 20 F2A nonmembers is settled by the FH-1 retirement census |

The FH-1 copies predate the public form. B1 adds no copies, so no file
gains a copy in this epoch and none crosses one fifth.

**Exclusions** (screen hits that are not members, with their dispositions
in `audits/b1-integration.md`, accepted by gate note 17):

- `uw_tail` (Relativization) → E3 `OracleNDTM.stepWith_eq_of_ne_qQuery`
  (OracleNondeterministic), 57%. Glue: shared citations of the
  fixed-choice step bridge.
- `uw_scan_step` → `uw_false_step` (Relativization, in-file), 71%. Glue:
  the shared `uw_step_scan` call line. It is also uncounted under the
  in-file convention.
- `Catalog.f2_loopBody_step` → `queryTM_init` (Classes), 54%. The
  configuration-equality idiom; no machine argument is shared.
- `runFrom_ofMultiTapeTM` → `runFrom_plainEmptyOracle` (Oracle, in-file),
  53%. A screen artifact: both declarations are unchanged (gate note 18).

So Relativization, Classes and OracleNondeterministic have no members.
`OracleNondeterministic`'s private blank-cell bound moved to `Oracle.lean`
as the public `queryString_length_le_of_blank` (C1-P1). Both consumers cite
it, so no copy remains (gate note 8).

## §12.8 statement layer (PR #28)

Added at the §12.8 statement gate, round 1 (`audits/s12-8-statements-findings.md`,
finding 8 and note 38).

- **Catalog's denominator** (2026-10-11). Part 3 adds 31 public declarations,
  none of them members, bringing Catalog to 459 declarations (75 public,
  384 private). The members are unchanged, so the fraction is now
  **318/459 = 69.3%**; strict, 283/459 = 61.7%. The R1-close figure of
  318/428 is the historical snapshot. The scheduled resolution is still the
  12.2c per-theme split.
- **Same-file similarities, not members.** The screen found twelve new pairs,
  all within a file. They are uncounted under the in-file convention:
  - the four seek tables among themselves, including `seekEndTM` ←
    `skipTM` at 100%;
  - `writeConstTM` ← `writeAdvTM` at 58%.

  These are distinct small transition tables over shared phase types, with
  different stop and return behaviour; no proof is copied (gate note 38). The
  fills must use the one shared trace that the sketches promise.
- **The new files** (`SymbolLift`, `Build/Scan`, `Build/InputCall`,
  `Build/CfgRecord`) have no members.

## Wave-1 statements (PR #43): §12.8b, §12.10, §12.11

Added at the wave-1 statement gate, round 2 (`audits/wave1-statements-findings.md`, finding 2;
`audits/wave1-statements-resolutions.md`).

**Round 1's copy-side member is gone.** `CertShell.certificateShell_proj` reproduced
`Nondeterminism`'s private `certificate_split_strictMono` (82/99). By user decision
(2026-10-11) it and both disclosed re-derivations were factored, not acknowledged:

| Mirror (round 1) | Shared home now | Re-derived from it |
|---|---|---|
| certificate split uniqueness and certificate-length monotonicity (`CertShell` against `Nondeterminism`) | `TuringMachine/ChoiceWords.lean`: `append_split_unique`, `certificateLength_strictMono`, `expCertificateLength_strictMono` | `CertShell.certificateShell_proj`, `Nondeterminism`'s split proofs (five privates removed) |
| W2-0, the query-length invariant (`OracleSim` against `Oracle`/`OracleNondeterministic` privates) | `Oracle.lean`: `OracleTM.step_radius`, `OracleTM.runFrom_radius` | W2-0, `Oracle.lean`'s initialized invariant, `runWith_headBlank` |
| the choice-word certificate law (`OracleSim.mem_iff_exists_choiceOut` against `Nondeterminism.choice_certificate_iff`) | `ChoiceWords.lean`: `choiceBudget_le`, `run_take_of_halted` | both laws (`acceptsWithin_iff_of_halts`, `mem_iff_exists_choiceOut`) |

**Members after round 2.** The five statement modules and `ChoiceWords` have no members.
`Nondeterminism`'s count does not grow.

**Exclusions** (screen hits that are not members; for the gate to rule on):
- `Nondeterminism.a3n_unpad_EXP` → `ChoiceWords.expCertificateLength_strictMono`, 82/130
  (63%). A pre-existing in-file pair: the base screen shows it against the former
  `e3_split_strictMono`, also at 63%. It became cross-file when the exponential monotonicity
  moved beside its polynomial sibling. The shared text is one monotone-power inequality
  (`Nat.mul_le_mul_left C (Nat.pow_le_pow_right … (Nat.pow_le_pow_left … c))`) inside an
  unrelated padding proof. No argument is copied.
- `ChoiceWords.certificateLength_strictMono` ↔ `expCertificateLength_strictMono`, 84% / 64%:
  an in-file pair, uncounted under the in-file convention. These are two monotonicity facts
  for two different length functions, NP and NEXP; the pair was in-file in `Nondeterminism`
  before.
- `CodeSimulator.tableBitsK` reproduced by the frozen serializers: `CodeFormat.oneTapeFormat`
  (85%), `CodeFormat.codeTable2Bits` (67%), `Codes2Tape.Code2TM.serialize` (56%),
  `UniversalInterpreter.universalRecords` (56%). This is the **item-8 residual family** (the
  generic writer against the frozen writers, which cannot be redefined), with the bridges
  `tableBitsK_two` and `oneTape_serialize_eq` proving the equalities; gate round 1, note 47.
  The `universalRecords` hit is the same family, visible once round 2 screened the
  `Universal*` files.

## Watch items (design-parallel, no byte-copies)

| Item | Status |
|---|---|
| **ch7 EmitIter layer vs the §12 layer** (merged with PR #11, 2026-10-10): `Build/EmitIterEmbed.lean` exports a **public** tape-padding, state-injecting embedding layer (`padAction`/`embedCfg`/`embed_step`/`embed_run`/`SafeRun` — 18 public declarations, none private; *corrected 2026-10-10: the first version of this row called them private*), written against main (which lacks `Build/Embed.lean`) and structurally parallel to the §12 bank-embedding transformers; the emit-iteration host (`Build/EmitIterBody.lean`, 20 declarations: 1 public, 19 private — corrected at ch7 fill gate round 2, R2-3) parallels the §12/Loop host family. **Body-level screen** (`audits/evidence/ch7/ch7-fill-duplication-screen.md`; the first version of this row rested on a name screen alone): **no copies of pre-existing repository material** — none of the §12 or loop-library material matches; the ch7 modules consume main's public `exists_emitLoopTM`/`exists_emitCallTM`/`exists_installCallTM` rows by citation. This row is design duplication; the stack's own copy family is ledgered below. | **12.2c docket** (user, 2026-10-10): harmonize to one embedding layer and one host family at the per-theme split; the naming of the shared block primitive is settled there too. The ch7 fill gate (`audits/ch7-fill-pack.md`, run on the merged tree; question 7) compares the two layers as facts. Consumption embargo until that gate closes. |
| **Pre-issue shared lemmas for epoch C1** (maintainer, 2026-10-10): `Turing.MultiTapeTM.spaceUsed_le_mul_succ` (`Finite.lean`) is the bound inside Catalog's private `f2_space_of_time`; `Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff` (`ClassNP/NTIME.lean`) is `DTIME_subset_NTIME`'s per-input content, which now cites it; `Complexity.SPACE.mono_const` and `Turing.FinTM.computesInSpace_zero_of_k_eq_zero` (`SpaceComplexity/Basic.lean`). They were landed so that C1a/C1b cite instead of copying. **Residual:** `f2_space_of_time` should become a citation of the public bound in 12.2c T3 (Catalog core). Also recorded for later tranches (item 11 dossier): private live-prefix copies of `runFrom_state_ne_none_of_le` in Catalog, Hardness and SAT, and Loop's `loop_input_run_le`, which equals the public `timed_input_bound` (removed in 11A) | Watch; T3 / T2 |

## Acknowledgment and disposition state

| Debt family | Acknowledgment | Cleanup owner and window |
|---|---|---|
| Catalog's 318 expanded members (↔ Primitives/Loop/Wrappers/Composition/TimeConstructible + in-file) | **D-R2** (user, 2026-10-09) | the **12.2c** per-theme refactor, promoted to the next window after R1; precondition (shrunken `Build/` files) met |
| **The §12 sibling rows' in-file repetition** (`transferTM`/`copyTM`/`clearTM`/`compareTM`/`incrementTM`, their traces, framed contracts, canonical rows and space rows; pass 3b and the copy-text screen). **Grown by the §12.6 fill:** 16 new directed pairs (5,520 matched characters), against 20 gone and a net −330 characters (`audits/evidence/s12-framed-fill/copytext-diff.txt`). Examples: transfer-framed → copy-framed 97%, and increment success → overflow 90% | **12.2c item 5** on the user-consolidated tasklist (2026-10-10). The §12.6 fill gate ruled the growth inside this acknowledged family, so a minor (`audits/s12-framed-fill-findings.md` F1/F2) | the user's **12.2c**, item 5: a common scanner. Its scope now explicitly includes the generalized traces, the framed consequence proofs, the canonical specializations and the space wrappers |
| Loop's 13 H3 copies (+1 near-copy) | **D-R3** (user, 2026-10-09) commissioned the collapse mechanism — §13 Z5, **now proved** (vhost-f1) | **ACKNOWLEDGED (user, 2026-10-09): retrofit batch RB4** (Loop), consuming Z5, window: after the A-S1 fill gate closes — **RB4 merged (PR #13, 2026-10-10): 12 of 13 H3 copies deleted by Z5 transfer; `emLoopHost_prepare` survives with a rewritten proof, still counted.** The inlined residue is the row "RB4's inlined residue in Loop" below |
| The three-file relocation family (4 decls × 3 files; pre-policy legacy, disclosed at its batches as "private harvest" but verbatim in fact) | **the user, 2026-10-09** (the round-2 audit's R2-2 disposition) | **ACKNOWLEDGED (user, 2026-10-09): the same RB4** (all three files), replacing the family with the R1 selected-tape exports (D-R1, proved) + Z5 agreement transfer, per the inventories' own analysis of what unlocks it — **RB4 (2026-10-10): Loop's 4 originals DELETED** (R1 embedding + injective state transport + Z5). **Primitives' and Hardness's 4 + 4 copies REMAIN.** Their generic interfaces are stronger than R1 (aliased host slots, non-injective state maps), so a literal replacement would weaken surviving statements. Continuation: **RB5 (revision 2, 2026-10-10)** promotes `runFrom_mapState_of_agreeOn` into `Build/Embed.lean` (it needs both `StateRenaming` and Z5, and only Embed already imports both), then specializes per concrete layout, Primitives before Hardness. **DISCHARGED (RB5, PR #14, merged by the user 2026-10-10):** all 12 family members are gone. Primitives' and Hardness's copies are deleted, and every relocation pair is gone from the copy-text screen (739 → 692 pairs over the four files, with no new pair). The census twin `f2_splitEmbed_run` in Catalog survives; it is now a special case of the public lemma, and 12.2c item 2 can replace it by a citation |
| **RB4's inlined residue in Loop** (post-merge copy-text finding, 2026-10-10): the forwarding host's consumers reproduce the original loop host's phase proofs. `emLoopHost_round` reproduces 100% of `loopHost_reject`; `emLoopHost_prepare` 99% of `loopHost_prepare` and 100% of `loopHost_input_rewind`; `emLoopHost_anchor_return` 95%; `emLoopHost_start` 92%. The frame pairs `emCall_bank_*` (94%) and `emCall_finish_*` (79%) grew more alike. In all, 11,476 characters of the forwarding host reproduce the original (`audits/evidence/retrofit/copy-text-screen.py`) | **ACKNOWLEDGED (user, 2026-10-10)**: RB4 accepted as merged, and RB5's Loop task withdrawn. The residue is not removable phase by phase: the `loopHost_*` lemmas state endpoints only, and the anchor-return phase runs in body control from `t = 0`, exactly where the two hosts differ (RB5's first dispatch kernel-checked the counterexample) | the user's **12.2c**, tasklist item 11: unify the two hosts structurally |
| **ch7 block stack's per-loop lemma family** (PR #11, 2026-10-10): the OR/XOR/majority loops re-prove one orbit/length/init/emit lemma set under renaming. **Census corrected at ch7 fill gate round 2 (R2-2) to the standing source-inclusive rule, as lower bounds:** `PolyTimeBlockTests` **≥ 12/25 (48%)**, `PolyTimeBlockMajority` **≥ 8/14 (57%)**, `PolyTimeBlockLoop` ≥ 1/32. The first record (4/14 and 2/25) counted copy sides only, and the round-2 auditor found four more cross-file adaptations, `anyStep`/`majStep`, `anyEmit`/`majEmit`, the orbit lemmas and the loop outputs (81–93%), plus two length correspondences (`audits/ch7-fill-r2-findings.md`). The pre-screen is `audits/evidence/ch7/ch7-fill-duplication-screen.md`, whose method description is corrected | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH7-D1**, opened under the one-fifth rule and answered. **Extension ACKNOWLEDGED (user, 2026-10-10, round 2)**: the enlarged family and the `PolyTimeBlockTests` threshold crossing | the **12.2c** per-theme refactor (the user's own window; colleagues spared deduplication work): one generic lemma set in `PolyTimeBlockLoop`, statements unchanged, coordinated with the ch7 owner, after the ch7 fill gate closes **DISCHARGED 2026-10-11** (12.2c T1 item 7, PR #18; gate CLOSED round 1, 0/0/3 minors swept): the generic layer `Complexity.BlockLoop`; census Tests 22/25 → 0/8, Majority 12/14 → 0/6, Loop 6/32 → 0/50; six-file screen 125 / 47,734 → 41 / 10,045. Residual: the excluded `length_xorPairStep_le`/`length_sliceDropAt_le` near-copy (watch). |
| **ch7 `EmitIterEmbed` run-infrastructure re-proofs** (ch7 fill gate round 2, R2-1): five facts are re-proved rather than cited, so **≥ 5/18 = 27.8%, over one fifth**. They are `step_output_prefix` and `runFrom_output_prefix` (Loop's private `emLoop_step_prefix`/`emLoop_run_prefix`), `runFrom_output_extends` (a specialization of `Finite`'s public `MultiTapeTM.output_prefix`), `runFrom_of_halted` (`Deterministic`'s public `runFrom_of_halt`), and `state_isSome_of_runFrom` (Loop's private `loop_live_prefix`). The screen missed all five because the proofs were restructured | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH7-D2** | the user's **12.2c**, item 6: one shared home for the run facts (output-prefix commutation and extension, halting absorption, live prefix) in `Deterministic.lean`/`Finite.lean`, beside `runFrom_of_halt`. `EmitIterEmbed`'s five become citations or re-exports, statements unchanged, and Loop's three private copies are deleted. Coordinated with the ch7 owner |
| **`Codes2Tape.lean`'s format-specific parse layer** (ZF-B/B2, 2026-10-10): 23/33 two-tape instances of `CodeParser.lean`'s one-tape top layer (69.7%; 3 strict) | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH34-D2** | the **12.2c** tasklist item 8: a format-parameterized parse layer (one-tape, two-tape, ND), statements unchanged. **DISCHARGED 2026-10-11** (PR #19, gate CLOSED round 1, 0/0/0): adaptations 23 → 1 (`zfBFallback`, approved residual); screen 117 / 29,824 → 77 / 12,563; all 44 CodeParser/Codes2Tape and 7 Codes2Tape/MathlibBridge pairs gone. Brief `briefs/ch34-t1-item8.md` (tranche T1); the generic layer's resemblance to the frozen one-tape definitions it bridges (`actionBitsK`↔`actionBits`, `codeSkipActionK`↔`codeSkipAction`, the table writer against the three frozen `serialize` bodies) is pre-named in the brief and stays as a residual watch item |

**R8.0b E1, the mandated `counterLoopTMVia`/`counterLoopTM` definition pair** (§12.8 stream D,
PR #38): `CounterLoop.counterLoopTMVia` reproduces 261/287 = 91% of the frozen
`counterLoopTM`, and 84% the other way. It is a definition pair that the R8.0b brief itself
mandated; there is no copied proof. **ACKNOWLEDGED (user, 2026-10-11)**, as a one-off exception
for exactly this pair (R8.0b gate finding F1). **Cleanup owner and window:** the maintainer, in
**12.2c**, through backlog §1 R80B-E1: redefine `counterLoopTM` as the identity-embedding
instance and re-check consumers. `CounterLoop`'s other new pair, `counterLoopTM_run_done`
↔ `_run_escape` at 83%/72%, is two Z5 re-derivations sharing transport setup. It is not a
member (gate note F8).

**RW-1, the rewind row's copies of Catalog's seek frame and skip-back table** (PR #138,
`Build/Rewind`, 2026-10-18). Two like-kind cross-file pairs, both against `Build/Catalog`:
- the private `rw_cfg` reproduces Catalog's private `catalogSeekCfg` at 79/79 = 100%, both ways:
  one record update over a different phase type; no proof is copied;
- `rewindTM` and `skipBackTM` share one contiguous 140-character block, 80% of `rewindTM`'s
  175-character body and 69% of `skipBackTM`'s 202: `rewindTM`'s table is `skipBackTM`'s
  without its first row, with `start` in the role of `gap`. Inside the same 140 characters,
  `rewindTM` also pairs with the seek tables `seekStartTM` (98 characters, 56% of `rewindTM`),
  `skipTM` (71, 55% of `skipTM`) and `seekEndTM` (92, 53% of `rewindTM`): the seek family's
  table pattern.

**Census** (the primary rule, each member counted once per file it inhabits; corrected at gate
55, finding 1: the first version counted `rw_cfg` alone, 1 of 5, and called the table pairs
design-parallel, an exception the rule does not make for cross-file pairs; the seek tables'
resemblance among themselves, §12.8 statement layer above, is uncounted only because it is
in-file):
- `Build/Rewind`, the copy side: **2 of 5 declarations (40%)** (3 public, 2 private), **20**
  lines in member blocks (`rewindTM` 14, `rw_cfg` 6), 219 characters reproduced. `RewindPhase`
  (a 48-character body, below the floor) and `rw_step` (no pair at half) are not members.
- `Build/Catalog`, the original side: **5 more members**, `catalogSeekCfg` (6 lines),
  `skipBackTM` (16), `skipTM` (13), `seekEndTM` (18) and `seekStartTM` (19), 72 lines; 5 of its
  505 declarations. The file's row is re-totalled at its next census.
- The v3 screen of the module, `Build/Catalog` and the exhaustive replay at #136's head (563
  declarations, 416 pairs) regenerates byte-identical at gate 55; screened against the whole
  library, `rewindTM` and `rw_cfg` pair with nothing else.

**Exclusion** (a screen hit that is not a member; an exception to the rule, approved by the user
on 2026-10-21): `rewindTM_run_ofCfg` → Catalog's private `a2_mapSetup_run`, 84/163 = 52%. The shared
text is two tiles, 50 and 34 characters, of the run-by-induction idiom
(`| succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih (` and
`, MultiTapeTM.runFrom_succ_eq_step'`); no setup argument is shared. Screened against the whole
library, the same idiom reaches half of 12 short run proofs in 10 files: `a2_mapSetup_run`,
`Universal`'s `timedFrame_run`, `Robustness/ObliviousSchedule`'s `maskedClock_lockstep`,
`decorateTM_run` and `parallelTM_run`, `Nondeterminism`'s `b2_unary_run`, `CircuitEvalRun`'s
`step_rej`, `Build/Seam`'s `seamCompTM_runFrom_left`, `TimeHierarchy/ClockMachine`'s
`kCfg_run`, `SymbolLift`'s `MultiTapeTM.liftSymbols_runFrom`, `Composition`'s
`controlCfg_run`, and `Build/NDHost`'s `wr_cfg_scan` (there the frame-read idiom). As with the
B1 exclusion of the configuration-equality idiom (above), it is recorded, not counted. Counted,
`Build/Rewind` would be 3/5 = 60%.

**The one-fifth rule** (`workflow.md` §4): `Build/Rewind` is past one fifth. Its §1 item is
`backlog.md` RW-1, opened and acknowledged on 2026-10-18, before gate 55's pack shipped, for the
frame alone; gate 55 widens it to the table. `Build/Catalog` was past one fifth already (D-R2).

**Acknowledgment.** The frame: **ACKNOWLEDGED (user, 2026-10-18)**, before gate 55. The table
and the exclusion: **ACKNOWLEDGED (user, 2026-10-21)** (gate 55, finding 1: the census at 40%,
the idiom hit excluded), with the retirement by unification below chosen over a frame-only one. **Cleanup owner
and window:** the user's dedup window, through backlog §1 RW-1, with Catalog's next edit: one
public frame over any state type, cited from both files; and one left-pass table, the rewind
being skip back entered at `gap`, with both framed runs derived from one public back-pass run.
After the retirement, neither file has a member from this family.

**BW-1, the buffer-word identities** (PR #140, `TuringMachine/BufferWords`, 2026-10-18): four of the
module's six public lemmas restate `Build/StepBlock`'s privates (`bufferTape_append_shift` ↔
`bufferTape_suffix`, `bufferTape_append_mid` ↔ `bufferTape_reads`, `bufferTape_eq_none_of_not_mem`
↔ `bufferTape_outside`, `bufferTape_unary` ↔ `bufferTape_unary`): the same statements, with
different proofs (the new ones read `bufferTape` only through its published equations). The
copy-text screen pairs none of them, so this is a restated-fact family, not a text copy.
**ACKNOWLEDGED (user, 2026-10-18)**, in the ruling that chose the public module. **Cleanup owner
and window:** the user's dedup window: `StepBlock` imports the module and its four privates are
deleted, their uses re-pointed. **Census** (the primary rule, each member counted once per file it
inhabits; corrected at gate 57, finding 1: the first version counted `StepBlock`'s side only,
without fractions or spans):
- `TuringMachine/BufferWords`, the original side: **4 of 6 declarations (66.7%)** (6 public,
  0 private; `_drop` and `_take` have no counterpart), **45** lines in member blocks
  (`_append_shift` 10, `_append_mid` 9, `_eq_none_of_not_mem` 10, `_unary` 16).
- `Build/StepBlock`, the copy side: **4 of 135 declarations (3.0%)** (64 public, 71 private),
  **42** lines (`bufferTape_unary` 11, `_outside` 7, `_reads` 16, `_suffix` 8).
- No copied characters: the v3 screen of the module, `Simulation`, `Build/StepBlock` and
  `Build/SeamLayout` (140 declarations, 32 pairs) pairs none of the eight, before and after
  #140's merge of the campaign branch (`7c963897`).

**The one-fifth rule** (`workflow.md` §4): `BufferWords` is past one fifth, and its §1 item is
`backlog.md` BW-1, opened and acknowledged on 2026-10-18, before gate 57's pack shipped.
`StepBlock` is under one fifth, and #140 leaves it byte-unchanged. After the retirement, neither
file has a member.

**IW-1, the window copier's interval patch** (PR #137, `Build/InputWindow`, 2026-10-21): the
private `iw_patch` is `Build/StepClock`'s public `wordPatch` at `Γ = Bool`: token for token after
renaming its binders (`tape`, `head`, `v` for `ct`, `cp`, `u`), and equal by `rfl`
(`@iw_patch = @wordPatch Bool`). One definition; no proof is copied. The same definition is also
`Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape` (written
pointwise), both from 2026-10-10; `wordPatch` (2026-10-14) is the public one. These four are the
**interval-patch family**: the tree and the open branches hold no other. The B6 F1 record named
`counterPatch` for the dedup window; `catalogTape` was not recorded before. The worker reported
"new copies: none" (`StepClock` was outside its screen population and its import context). The
maintainer disclosed the copy in gate 54's pack (question 6), and gate 54's finding 1 made it a
debt major. **Not members:** `iw_patch_append` appends one cell (Catalog's public
`catalog_write_take` states the same fact in take form, with its own proof), and `iw_patch_true`
reads the patch at the all-true word (the `Bool` case of a step inside `CounterLoop`'s proof, not
a declaration). **ACKNOWLEDGED (user, 2026-10-21)**, at gate 54, for the whole family. **Cleanup
owner and window:** the user's dedup window, through backlog §1 IW-1: `wordPatch` moves below
`Build/Catalog` with Catalog's next edit, and the three private copies re-point to it
(`InputWindow`'s re-proofs are verified at gate 54's review). **Census** (the primary rule, each
member counted once per file it inhabits; declarations as the style lint counts them; lines by
the span rule):
- `Build/InputWindow`, a copy: **1 of 17 declarations (5.9%)** (1 public, 16 private), **5**
  lines (`iw_patch`).
- `Build/StepClock`, the public one: **1 of 41 (2.4%)** (8 public, 33 private), **4** lines
  (`wordPatch`). From #139 on, **1 of 42 (2.4%)** (9 public): #139 adds `wordPatch_append`, a
  member of WA-1 below.
- `Build/CounterLoop`: **1 of 79 (1.3%)** (59 public, 20 private), **4** lines (`counterPatch`).
- `Build/Catalog`: **1 of 505 (0.2%)** (113 public, 392 private), **5** lines (`catalogTape`). It
  is in none of the correspondences behind Catalog's row above, so it adds one member there.
- Copied characters: none by the v3 screen, which pairs none of the four. After renaming, each
  is the same definition of 175 to 199 characters.

**The one-fifth rule** (`workflow.md` §4): no file of the family is past one fifth.
`InputWindow` had no earlier copies. `Catalog` had, but #137 adds no copy to it, since
`catalogTape` predates the delivery. The §1 item IW-1 is opened anyway, as for RW-1, and
answered. After the retirement only `wordPatch` remains, in its new home.

**WA-1, the adjacent-patch law** (PR #139, `Build/StepClock`, 2026-10-18; ledgered at gate 56,
finding 2): the public `wordPatch_append`,
`wordPatch (wordPatch ct cp u) (cp + u.length) v = wordPatch ct cp (u ++ v)`, restates
`Build/RecordTable`'s private `rt_adjacentWrites` (2026-10-13). With `wordPatch` unfolded and
beta-reduced, the two elaborated statements are alpha-equivalent: they differ only in binder
names (`tape`, `o` for `ct`, `cp`), checked on the compiled declarations at #139's merged head
(gate 56's review). The proofs differ (the new one reads `wordPatch` and `FinTM.bufferTape` only
through their published equations; `rt_adjacentWrites` unfolds `FinTM.bufferTape`), and the v3
screen pairs neither, so this is a restated-fact family, not a text copy, as BW-1 is. The F3 review
that proposed the lemma disclosed the pair, and the ruling that chose it named it (backlog §2, F3
cont1: "E2 ruled (user, 2026-10-18): B"), but it was not ledgered until gate 56.
**Acknowledgment:** the ruling of 2026-10-18 that chose option B (F3's E2). The decision put to
the user named the re-point ("which also opens the `rt_adjacentWrites` re-point"), and the
ruling's record names `rt_adjacentWrites` as the lemma's private form, to re-point in the user's
dedup window. The record does not call the pair a copy family, as the same day's BW-1 ruling
does; gate 56's review (finding 2) reads the ruling as acknowledging it. **Confirmed (user,
2026-10-22):** the ruling acknowledges the pair. **Cleanup owner and window:**
the user's dedup window, through backlog §1 WA-1, with IW-1's move: once `wordPatch`, its cell
lemmas, `wordPatch_append` and the explicit-form lemma are below `Build/Catalog`, they are in
`RecordTable`'s closure; `rt_adjacentWrites` is deleted, and its one use (`rt_advanceCfg_append`)
cites `wordPatch_append`. **Census** (the primary rule, each member counted once per file it
inhabits; declarations as the style lint counts them at #139's merged head `1cd66f1b`; lines by
the span rule):
- `Build/StepClock`, the public one: **1 of 42 declarations (2.4%)** (9 public, 33 private),
  **25** lines (`wordPatch_append`). With IW-1's `wordPatch` (4 lines), the file has **2 members
  of 42 (4.8%)**, **29** lines.
- `Build/RecordTable`, the private one: **1 of 129 (0.8%)** (29 public, 100 private), **28** lines
  (`rt_adjacentWrites`). It had no member before.
- Copied characters: none. The v3 screen of `StepClock`, `RecordTable`, `WindowClock` and
  `WindowRun` (176 declarations, 19 pairs) pairs neither.

**The one-fifth rule** (`workflow.md` §4): neither file is past one fifth. #139 adds no copy to a
file that received copies before: `StepClock`'s earlier member is IW-1's `wordPatch`, the public
original, and #139 leaves `RecordTable` byte-unchanged. The §1 item WA-1 is opened anyway, as for
RW-1 and IW-1, and answered. After the retirement only `wordPatch_append` remains, in
`wordPatch`'s new home.

**C1-E cont1, the exhaustive replay** (PR #136, `ClassNP/ExhaustiveReplay`, 2026-10-21): **no
member.** The v3 screen's 122 new pairs are all in-file (0 cross-file, 0 gone; 297 → 428
declarations, 106 → 228 pairs). 26 are at or above the brief's 90% copy threshold, between 17 of
the module's 185 declarations (9.2%): the twenty `xr_*_ne_*` one-liners, two pairs of leaf tables,
two buffer-tape facts and the replay's two exits. They are disclosed in-file siblings, listed and
justified by family in the worker's report (§8) and qualified by its erratum
(`campaign/fills/c1/reports/exhaustive-2-ERRATUM.md`); gate 53 (minor 2, note 12) found no copied
material needing acknowledgment. Their consolidation, and the re-points to the public lemmas that
arrived after the fill's base, are `backlog.md` §1 C1E-1, in the user's dedup window.

**IR-1, the input rewind family** (megafill A, 2026-10-22). Four private input rewinds, each
with its own exact-time run proof:
- `ClassNP/ExhaustiveReplay`'s `xr_inRewindTM` (#136) and UN cont1's `un_inRewTM`
  (`Diagonalization/NTimeHierarchy`, 61% and 59% on the v3 screen): a cross-file pair, which the
  UN brief forbids;
- U2-S cont1's `ss_inputRewind` (`UniversalK`, #147);
- R cont2's `ic_rewind_scan` (`TuringMachine/NDCodeSimulator`), which re-proves the public
  `Turing.FinTM.rewind_scan` (51%; `Simulation` was outside that brief's screen population, so the
  worker's screen could not see it).

With them, UN's `un_mapState_comp` shares field-equation proof text with `ExhaustiveReplay`'s
`xr_E_initCfg` (54%; their statements differ: gate 65, minor 3).
**Acknowledgment and disposition (user, 2026-10-22):** UN's two pairs are resolved by **an API PR
first**: a public input rewind with an exact time and a first-visit cut, and a `mapState`
collapse lemma. UN's landing re-points to them. R's copy lands ledgered and re-points when that
API lands. U2-S's and `ExhaustiveReplay`'s are re-pointed in the user's dedup window.
**The API: #153** (2026-10-22): `Build/InputRewind`'s `Turing.inputRewindTM` and
`inputRewindTM_run`, and `Turing.Cfg.mapState_mapState`. Its v3 screen pairs the machine with
`xr_inRewindTM` (82% and 73%), and the lemma's proof text with `xr_E_initCfg`'s (54%; a shared
idiom, not a restatement: the composition lemma alone does not replace `xr_E_initCfg`); both are
in the dedup window, as above.
**Retirements (2026-10-23):** NDHost's `guessRun_mapState_mapState` with #153; R's
`ic_rewindLeafTM`, `ic_rewind_scan` and `ic_rewind_leaf_run` with #151; the canonizer's
`canonGramMapComp` with #152; UN's `un_inRewTM`, `un_inRew_run` and `un_mapState_comp` with #154
(its landing). Remaining in IR-1: `ExhaustiveReplay`'s `xr_inRewindTM` and `xr_E_initCfg` and U2-S's
`ss_inputRewind` (`UniversalK`), in the user's dedup window. A fifth copy found while building it, `Build/NDHost`'s private
`guessRun_mapState_mapState` (the lemma's exact statement), is removed in #153 (the user's ruling).
A sixth, found 2026-10-23 on #152's branch: the canonizer's private `canonGramMapComp`
(`TuringMachine/CodeSimulator`), the lemma's statement with the composite as `fun s => g (f s)`,
used at two `rw` sites; 99% each way on the v3 screen. **Disposition (user, 2026-10-23): re-pointed
at #152's landing** (prepared locally, `local/canon-mapcomp-repoint`), as for R's leaf.

**CC7-1, the canonizer cont7's in-file families** (megafill A item 3, `TuringMachine/CodeSimulator`,
2026-10-22). 59 new in-file pairs, none cross-file. Four are at or above 90%:
`canonGramCut_leg`/`canonStageCut_leg` (97% each way), `canonStageLeg4` → `canonStageLeg1` (94%)
and `canonStageLeg5` → `canonStageLeg1` (91%). Three families: the cut leg, the leg template and
the per-record bound. **Acknowledged (user, 2026-10-22): recorded as debt**, for the user's dedup
window, together with the retirement of the now-unused `canonCounterRepeat` link (the user,
2026-10-22).
**Census** (gate 67, minor 3; the primary rule, each member counted once per file it inhabits;
declarations as the style lint counts them; lines by the span rule, at #152's head `aed162fd`):
- the members, by family (11):
  - the cut leg (2): `canonGramCut_leg` (lines 7564–7585, 22), `canonStageCut_leg` (6332–6352,
    21);
  - the leg template (7): `canonStageLeg0`–`canonStageLeg6` (6354–7046: 90, 86, 91, 109, 106,
    98 and 107 lines);
  - the per-record bound (2): `canonStageBlock_consumes` (5669–5687, 19) and the base's frozen
    private `skipTable_consumes` (233–245, 13), whose local per-record bound it re-proves (61%);
- with IR-1's `canonGramMapComp` (7595–7607, 13), a cross-file member until #152's landing
  re-points it.

`TuringMachine/CodeSimulator`: **12 of 198 declarations (6.1%)** at the head (12 public, 186
private), **775** lines in member blocks; after the re-point, **11 of 197 (5.6%)**, **762** lines.
The file had no earlier ledger member: the item-8 entry's `tableBitsK` now lives in
`Build/StepBlock`. The review's other new in-file pairs, those not between two members of these
families, are screen matches, not members: all below 90%, between declarations with different
statements. **The one-fifth rule** (`workflow.md` §4): not reached.

**SD-1, the suffix drop** (PR #161, U2's API, 2026-10-24). One fact,
`(pairEncode u x).drop (2 * u.length + 2) = x`, in four files:
- `Turing.pairEncode_drop` (public, `Build/InputDevice`, line 198, new in #161), the one U2 cites;
- `NDCodeSimulator`'s private `ic_input_suffix` (line 340): the same statement and proof, 100% each
  way on the v3 screen (#161's evidence). **Retired** (2026-10-25): #162 moved it into
  `Build/InterpreterStartup` as the private `is_input_suffix`, and gate 74's round 2 deleted it
  there, the window call citing `Turing.pairEncode_drop` (the kit imports `Build/InputDevice`);
- `Complexity.Codec.pe_drop` (public, `SpaceComplexity/Codec/Parse`, line 69) and `PathWalk`'s
  private `drop_pairEncode` (line 225): the same statement through `pairEncode_eq_dbl`, different
  proofs (no screen pair).

*Historical (at #161's opening):* none of the four files could cite another's without a new import
(`InputDevice` was upstream of none of `NDCodeSimulator`, `Codec/Parse`, `PathWalk`). **Acknowledged
(user, 2026-10-24)**: the U2 review's F2 recommendation (publish `pairEncode_drop` with the API PR,
ledger the family) was the ruling's content. **Disposition:** the startup-kit re-point is **done**
(gate 74's round 2): the kit imports `Build/InputDevice`, so `NDCodeSimulator` sees it through the
kit, and the window call cites `Turing.pairEncode_drop`. Only the `Codec/Parse` and `PathWalk`
members remain, for the user's dedup window: one home beside `pairEncode_eq` in `Encoding` (a large
replay, hence the window). **Census** (one member per file): `InputDevice` 1 of 57 declarations
(1.8%), `Codec/Parse` 1 of 16 (6.3%), `PathWalk` 1 of 32 (3.1%); `NDCodeSimulator` and
`Build/InterpreterStartup` 0 since gate 74's round 2. The one-fifth rule is not reached.

**SK-1, U2-S's capture start** (PR #162, the startup-kit API PR, 2026-10-24). The kit's public
`Turing.embedSilentCfg_initCfg` (`Build/InterpreterStartup`) is U2-S's private
`ss_captureInitial` (`UniversalK`, line 329), harvested verbatim: 100% each way on the v3 screen.
`UniversalK` cannot cite the kit until `CodeSimulator` imports it (B5a's landing). U2-S's other
`ss_` startup pieces are the kit's constructions under other contracts (no screen pair). **By the
ruling (2026-10-24, the B5a review's recommendation)** they go to the user's dedup window, or to
U2's fill once `UniversalK` sees the kit. **Census** (gate 74, major 1, corrected at its round 2):
`Build/InterpreterStartup` 1 of 8 declarations (12.5%), the public `embedSilentCfg_initCfg`, 40
lines with its docstring; `UniversalK` 1 of 51 (2.0%), the private `ss_captureInitial`, 39 lines.
Round 1's kit had a second member, SD-1's suffix drop (2 of 9, 22.2%, past the one-fifth rule);
round 2 deleted it (SD-1 above), so the rule is not reached.

**RI-1, the round iteration along a sequence** (§13d G4 continuation 4, its review's F2,
2026-10-25). `Build/ZoneRebalance`'s private `zr_pinLoop` (line 8266, 71 lines with its docstring)
iterates pinned rounds by its own induction (`Round.segment`, then `Segment.trans`), which is the
proof of the published `Turing.Round.iterate` (`Build/Contract/Basic`, line 781), along the sequence
of pass indices `nxt^[m] j₀` instead of the configuration orbit `roundOrbit`. No published lemma
states the sequence form, so it re-derives `Round.iterate`'s argument, not its statement (the text
screen pairs nothing). All seven of the found path's passes go through it (`zr_passContract`). **The
ruling (user, 2026-10-25): land G4 with this entry; then an API PR adds the sequence form to
`Build/Contract/Basic`, with `Round.iterate` as its corollary, and re-points `zr_pinLoop` to it.**
Census (one member per file; the source side added at gate 75's minor 5): `Build/ZoneRebalance` 1 of
871 declarations (0.1%), the private `zr_pinLoop`, 71 lines with its docstring;
`Build/Contract/Basic` 1 of 85 (84 public, 1 private; 1.2%), the public `Turing.Round.iterate`, 18
lines with its docstring. The one-fifth rule is not reached. **The API PR is #167** (gate 78,
2026-10-25; stacked on #165): `Turing.Round.iterate_seq` beside `Round.iterate`, which becomes its
corollary, and `zr_pinLoop` re-pointed to it. On its landing RI-1 is retired. **Retired
(2026-10-26):** #167 merged as `4c8c2e7e`; `zr_pinLoop` cites `Round.iterate_seq`.

**SG-1, segment concatenation over a private segment predicate** (gate 98's finding 1,
2026-11-06). Two private predicates restate `Turing.Segment` (`Build/Contract/Basic`) at fixed
parameters, and each has its own concatenation lemma re-proving `Segment.trans`:
- `ClassNP/Tautology`'s `tautDualSegment c d t` is `Segment tautDualTM.tm {some .anchor}
  (fun _ => True) c d t`; `tautDual_segment_add` repeats `Segment.trans`'s endpoint and
  forbidden-prefix argument (the v3 screen pairs it with `Segment.trans`, 91/168, 54%);
- `Build/CounterLoop`'s `counterSpan` is a segment from `z` to its run endpoint over
  `{some .done, some .escape}`, whose head relation combines the counter head's interval and the
  body heads' `R`; `counter_span_append` repeats `Segment.trans`, then `Segment.mono` for the
  two relations.

Both predate #202 (the API PR whose gate found them); #202 adds no member. **ACKNOWLEDGED by kind
(the user, 2026-11-06):** every private predicate that restates `Turing.Segment` at fixed
parameters, with its concatenation lemma. **Cleanup owner and window:** the maintainer, in the
dedup window (12.2c): a bridge `tautDualSegment c d t ↔ Segment …` (and the same for
`counterSpan`), then `Segment.trans`/`Segment.mono` through it, deleting both concatenation
lemmas. **Census** (gate 98's, each member counted once per file; the source side included):
- `Build/Contract/Basic`, the public source: **1 of 93 (1.1%)**, `Segment.trans`, 20 lines;
- `ClassNP/Tautology`: **1 of 93 (1.1%)**, `tautDual_segment_add`, 12 lines. The file has no other
  recorded member;
- `Build/CounterLoop`: **1 of 79 (1.3%)**, `counter_span_append`, 28 lines. The file's
  recorded total, every acknowledged member counted once (corrected at gate 98's round-2 minor
  1): SG-1's `counter_span_append`, IW-1's `counterPatch` and R8.0b E1's pair `counterLoopTM`/
  `counterLoopTMVia`, **4 of 79 (5.1%)**, 68 lines (28 + 4 + 19 + 17).

**The one-fifth rule** (`workflow.md` §4): no file of the family is past one fifth.

**The window (2026-11-06):** `CounterLoop`'s member is retired by #215 (`57939a97`: a private bridge
`counterSpan_iff_segment`; `counter_span_append` deleted; its three uses through `Segment.trans`
and `Segment.mono`). The scope search found a **third member**, `Robustness/SingleTape`'s private
`DGSpan` (`Segment tm ∅ (lo ≤ p 0 ≤ hi) c d t`) with `dgSpan_add` (7 uses). `Tautology`'s and
`SingleTape`'s members need a new import of `Build/Contract/Basic` (cycle-free; it adds that one
module to each closure): **parked for the user's ruling.** Also found, not counted: `Primitives`'
`splitSafe`/`splitSafe_add` and `Catalog`'s `f2_splitSafe`/`f2_splitSafe_add` restate
`Turing.SafeSegment` (a sibling `SafeSegment` family, for the user); `SAT`'s `sat_guard_add` and
`Hardness`' `clA5_guard_add` re-prove the cut half of `Segment.trans` with no predicate. If
`tautDual_segment_add` is deleted, `blueprint/src/chapter/Complexity/ClassNP/Tautology.tex:981`
changes with it.

**BL-2, the binary width of an incremented register value** (gate 101's finding 1,
2026-11-06). The bound `m ≤ 2 ^ e + 1 → |Nat.bits (m + 1)| ≤ e + 2`, through
`m + 1 < 4 · 2 ^ e = 2 ^ (e + 2)` and BL-1 (i)'s `length_bits_le`, was proved three times:
- `Logspace/ISCountGenCorrect`'s private `bits_succ_le` (BL-1 (i) lists it as a site that cites
  `length_bits_le`; its successor/exponential step is this family's);
- `Machines/ARMWidth`'s `arm_decides_pspace_val`, an inline `hlt` block at `N = C₀ (|x| + 1)^c₀`;
- `SavitchARM/Deepen`'s `deepen_contract` (new in #208), the same block at `W · W`.

Census (gate 101's, one member in each file): `Deepen` 1 of 45, `ARMWidth` 1 of 5,
`ISCountGenCorrect` 1 of 9. No file is past one fifth (`ARMWidth`'s 1 of 5 is at it).
**Ruled (the user, 2026-11-06): harvest in #208, all three.** `#208`'s commit `9db4f2ee`
publishes `Complexity.LogProg.length_bits_succ_le` in `Machines/Bin`, beside `length_bits_le`;
`bits_succ_le` is deleted, and the two inline blocks cite it. A library search for the
`4 · 2 ^ e` step (`2 ^ (… + 2) = 4 * 2 ^ …`) finds no other member: `ExpBFS/Main:535–539`
bounds a `Nat.log` width and a memory range, and `BinaryArith/AddSub:174` a sum of two words, both
other statements. **Retired on #208's merge.**

**IL-1, the input-length decider's answer** (gate 101's round-2 screen, 2026-11-06). The
public `Complexity.indicator_inputLenLang` (`Logspace/InputAccess`, since the ARM dedup `56716442`)
states that `inputLenLang` answers `decide (a < |y|)` on `pairEncode y (bits a)`. Six proofs
unfolded their decider table and repeated its two-line proof
(`inputLenLang`, `indicator_indexLang_pairEncode`, `decide_eq_decide.mpr Iff.rfl`):
- `Logspace/ISCountGenCorrect`'s `gen_start` (`hq`), which the v3 screen pairs with
  `indicator_inputLenLang` and with `ExpBFS/Main`'s `orcN_len` at 94%;
- `ExpBFS/Main`'s `orcN_len`, `SavitchARM/Correct`'s `hq`, `Machines/ARMWidthExample`'s `hq`,
  `Logspace/PathHardRegs`' `orc_len` and `Randomized/SpaceAmplifyPoly`'s input-length loop (each
  under the screen's cut-off or outside its population; found by `git grep` for the closing step).

All six predate #208; `Deepen` cites the lemma. Census: one member in each file. No file is past
one fifth. **Ruled (the user, 2026-11-06): re-point all six in #208.** #208's commit `6a289c50`
replaces each by the table's unfolding and `indicator_inputLenLang`; each file elaborates.

**Widened by kind (2026-11-06):** every proof that re-derives one of `InputAccess`'s two
published readings, `indicator_inputLenLang` or `indicator_inputBitLang`
(`y.getD a false` on `pairEncode y (bits a)`), by unfolding the language and
`indicator_indexLang_pairEncode`. The first search matched only the `decide_eq_decide` closing;
its simp-set variants are five more members: `PathWalkMachine`'s `pathOr_len` and `pathOr_bit`,
`PathHardRegs`' `orc_bit`, and both halves of `Mult`'s private `mult_queries`. **Ruled (the
user, 2026-11-06): re-point all five in #208**, done at `0140aee2`. A grep of every code line
naming `inputBitLang` or `inputLenLang` finds no other unfolding: `TQBFARM/Machine`'s and
`Codec/Run`'s `orc_bit`/`orc_len` and `QueryReshape`'s `drop_bit`/`drop_len` already cite the
lemmas. The other readers of `indicator_indexLang_pairEncode` (`QueryReshape`'s
`drop_lang_pair`, `comp_lang_pair` and `transport`; `PathHardDecide`'s `qLang` step) read other
languages, which have no published reading; they are not members. Census after widening (corrected
at gate 101's round-2 minor 1): **10 declarations across eight files, 11 proof sites**:
`PathHardRegs` (`orc_len`, `orc_bit`, 2 of 62) and `PathWalkMachine` (`pathOr_len`,
`pathOr_bit`) two declarations each, `Mult`'s `mult_queries` two sites in one declaration, every
other file one. No file is past one fifth. **Retired on #208's merge.**

**NZ-1, no machine halts in zero steps** (found 2026-11-06 in gate 102's round-1 search; widened
by kind in its round 2; **acknowledged, the user 2026-11-06: publish and re-point now**; PR #217,
`lean/dedup-nz1`, commits `5e77e558` and `2fdb84f7`). One fact in two readings: the initial
configuration is live, so no run halts within `0` steps.
- **Deterministic:** public as `Turing.FinTM.not_computesInTime_zero` (`TuringMachine/Finite`).
  Already cited by `ClassP/DTIME`, `ClassNP/TMSAT`, `CookLevin/Hardness` and
  `Diagonalization/EXPCOM`, and since #211 by `TwoTapes`' `tt_forward_run`. Re-derived (gate 102
  r2, finding 1) in `Build/Loop`'s private `emCall_prepared_eval_first` and `CircuitComplexity/Advice`'s
  `DTIMEAdvice_eq_empty_of_eq_zero`; #217 re-points both.
- **Nondeterministic:** no public lemma before #217, which publishes `Turing.NDTM.not_haltsWithin_zero`
  (`TuringMachine/Nondeterministic`). Its five copies, one per file: `ClassNP/ExhaustiveReplay`'s private
  `xr_not_haltsWithin_zero` (deleted), `ClassNP/NDNormalForm`'s `nf_forward` (`hpos`), `ClassNP/NTIME`'s
  `NTIME_eq_empty_of_exists_zero`, `Randomized/ExpectedTime`'s `AbortDecidesInTime.restart`,
  `Randomized/BPTIMEThreshold`'s `BPDecidesInTimeWith.one_le`; #217 re-points all five. **+1 (gate 108,
  minor 1):** `Randomized/ExpectedTime`'s `notHaltedProb_haltRun_zero` (the probability form);
  re-pointed in #217. Census: 8 sites (6 nondeterministic in 5 files, 2 deterministic).

**The search** (by kind, at `1dd510aa`): `rw`/`simp`/`change … at` forms with `runFrom_zero`,
`runWith_nil`, `initCfg`, `Cfg.init` or `init_state`; zero-case scans (`by_contra`,
`Nat.pos_of_ne_zero`, `eq_zero_or_pos`, `| zero`) near initial-configuration terms; `[] rfl` and
`[] (by …)` instantiations of halting hypotheses; literal time-0 `runFrom`/`ComputesInTime`/`HaltsWithin`;
`show`/`change`; and, after gate 108, probability and expected-time forms and `simp` closures without `at`. **Not members**, each a different fact: first-halt helpers from an arbitrary `cfg`
(`Loop:219`, `Catalog:6463`, `SAT:3797`, `Hardness:6176`); runs from non-initial configurations
ending in a state mismatch (`Hardness`, `NDCodeSimulator`, `NDNormalForm`, `StepBlockLoop`,
`Contract/Basic`, `Contract/Seam`, `NTimeDiagonalizer`); composite runs at positive times
(`UniversalK`, `NTimeHierarchy`, `Composition`, `Inclusions`); positive liveness facts
(`state = some q₀`); and other models (NARM's `narun`, `Yap`'s `badLang`, the oracle machines).
**Retired: #217 merged 2026-11-06 (`eb8cbf60`).**

**TC-1, the copying transducer state** (PR #164, A1, 2026-10-25; gate 76's note 7). One fact, a
transducer started in a state that copies every bit and is kept is the identity, in three files:
- `Complexity.transduce_of_copy` (public, `ClassNP/Transducer`, line 83, new in #164), the general
  form: from `∀ b, δ q b = q` and `∀ b, o q b = some b`, `transduce δ o q l = l`;
- `Complexity.KarpLipton.transduce_drop_true` (public, `CircuitComplexity/KarpLiptonPrefix`, line
  87) and `Complexity.Meyer.transduce_fT_copy` (public, `CircuitComplexity/MeyerVerifierGlue`,
  line 145): its instances at `q = true` and `q = none`, each the general lemma with `fun _ => rfl`
  twice (the megafill D review's `probe/A1ConsumerProbe`; gate 76 checked both specializations),
  each re-proved by its own induction.

Both instance files import `ClassNP/Transducer`, so each can cite the general form.
`spaceConstructible_poly`'s landing cites it (`Savitch`'s private `scp_transduce_copy` is the
one-line application), which avoids a third copy. **The ruling (user, 2026-10-25, Q-D2): include
the general form in A1; re-point the two instances in the user's dedup window (12.2c), since that
edits `CircuitComplexity/*`.** Census (one member per file, at A1's head): `ClassNP/Transducer` 1 of
10 declarations (10.0%), `KarpLiptonPrefix` 1 of 16 (6.3%), `MeyerVerifierGlue` 1 of 42 (2.4%). The
one-fifth rule is not reached.

**RS-1, the restart identity** (PR #170, B5a's landing, 2026-10-27; disclosed in gate 81's pack,
item 4; completed by gate 81's finding 1). One fact: a machine whose initial state is a relabelled
`q` starts in the relabelled blank configuration at `q`, i.e.
`B.q₀ = f A.q₀ → B.initCfg x = (A.initCfg x).mapState f`. It is proved at five sites in four
files, each by `Cfg.ext` with the `Cfg.init_*` and `Cfg.mapState_*` field equations:
- `Turing.UniversalK`'s `uk_init_mapState` (private, line 1816), the general form, used twice
  (`uk_loop_init`, the suffix startup);
- `Turing.UniversalK`'s `exists_selfStartupTMK` (public, line 1425): its local `hinit`
  (line 1584), `R.initCfg (pairEncode α w) = d₀.mapState Sum.inl` with
  `R := { W with q₀ := Sum.inl A.q₀ }` (gate 81's finding 1);
- `CodeSimulator`'s `us_start` (private, line 8984 at #170's head), its instance at
  `{ W with q₀ := Sum.inl entry }`, after `MultiTapeTM.initCfg_with_q₀`;
- `ExhaustiveReplay`'s `xr_E_initCfg` (private, line 3133), its instance at a doubled `Sum.inl`
  with the host's blank fields;
- `NTimeHierarchy`'s `un_setup` (private, line 604): its local `hstart` (line 1410), the instance
  at a seven-fold `Sum.inl` of the embedded blank start `c0`.
**Partly published (the user, 2026-11-06):** the U2 harvest publishes it as `Turing.MultiTapeTM.initCfg_eq_mapState` in `Build/UniversalParts` (both of `UniversalK`'s uses now cite it). The other sites re-point to it in the dedup window, without a move to `Finite`.

Census (one member per file; each count at the tree named): `CodeSimulator` 1 of 208 declarations at
#170's head (12 public, 196 private; 0.5%), `ExhaustiveReplay` 1 of 185 (0.5%), `UniversalK` 2 of 79
(2.5%), `NTimeHierarchy` 1 of 15 at the campaign tip before #172 (6.7%), 1 of 25 after it (4.0%;
cumulative with TR-1 below). The one-fifth rule is not reached. **Disposition** (gate 81's finding
1: publication need not precede #170 under D1(A)): a public row beside `MultiTapeTM.initCfg_with_q₀`
(`TuringMachine/Finite`) in the user's dedup window (12.2c), with the five sites re-pointed.

**PL-1, the linear-to-polynomial lift, and WT-1's residue** (PR #171, the word tests, 2026-10-27;
disclosed in gate 82's pack, item 5). Two copies outside the ruling's scope (E-DUP covered the
fixed-word and all-`true` tests only):
- `Nondeterminism`'s private `a3n_poly_linear` (line 3537 at #171's head `d17f63c8`; 13 uses) and
  `a3n_poly_const` (line 3544), equal in their proofs, up to the names, to the public
  `Complexity.polyTimeComputable_of_linear` and `Complexity.polyTimeComputable_const`
  (`ClassNP/PolyTimePairing`, lines 64 and 71). `Nondeterminism` does not import `PolyTimePairing`;
  the import is acyclic (`PolyTimePairing` imports only `ClassNP/PolyTime` and `Build/Primitives`).
- `Savitch`'s inline `hD'` (`SpaceComplexity/Savitch`, line 193 in `spaceConstructible_poly`'s
  proof): the conversion of `computesFunInTime_ifEq [] [true] [false]` to `[decide (x = [])]`,
  which is `Turing.FinTM.computesFunInTime_decideEq []` (#171). An inline step, not a declaration.
  **Re-pointed by #175's round-1 fix** (gate 86's finding 2, user, 2026-10-27): the proof, now in
  `Constructible`, takes its decider from `computesFunInTime_decideEq []`; no copy is left there.
- `SAT`'s private `sat_pt_eq` (line 2886) and `CookLevin/Hardness`'s private `clA5_pt_eq` (line
  6818), twins (found by gate 82's resolution of its finding 1): each lifts
  `computesFunInTime_ifEq w [true] [false]`, converts it to `[decide (x = w)]` and composes it with
  a polynomial field map. Each is `polyTimeComputable_of_linear (computesFunInTime_decideEq w)`
  composed with that map.

Census (one member per file, at #171's head): `Nondeterminism` 2 of 199 declarations (8 public, 191
private; 1.0%), `PolyTimePairing` 2 of 26 (7.7%; the public originals), `SAT` 1 of 270 (0.4%),
`CookLevin/Hardness` 1 of 545 (0.2%). **Corrected (gate 86's finding 2, 2026-10-27):** the census
omitted the fixed-word test's public original, `Build/WordTests`'s `computesFunInTime_decideEq`,
**1 of 4 declarations (25%)**, so the source-inclusive count crosses one fifth in `WordTests`.
**Human review (user, 2026-10-27): accepted** — a four-declaration module whose member is the
public row the copies should cite; the consumers' re-points retire the family. **Disposition:** the
user's dedup window (12.2c): re-point the two privates to the public rows (one import), and the
twins to `computesFunInTime_decideEq w` (each with the import of `Build/WordTests`); `hD'` is
re-pointed already (#175).

**TR-1, the truncation of an acceptance at an all-branch budget** (PR #172, H's landing,
2026-10-27; the H brief review's F1 and gate 84's pack, item 5). One fact: if every branch of `N`
on `x` halts within `T`, an acceptance at any length is an acceptance within `T` (and conversely
by `AcceptsWithin.mono`). It is stated privately in three files:
- `Nondeterminism`'s `acceptsWithin_iff_of_halts` (line 165), through the published
  `Turing.run_take_of_halted`;
- `ExhaustiveReplay`'s `xr_accepts_iff_of_halts` (line 134);
- `NTimeHierarchy`'s `nh_accepts_of_halts` (new in #172), through `run_take_of_halted`. The
  user's D1 (A) licensed this leaf; the v3 screen pairs it with the first at 61%.

`ClassNP/NTIME`'s `NTIME.mono` does the same truncation inline. Census (one member per file, at
#172's head `33d68537`, a tree before #171): `Nondeterminism` 1 of 201 (8 public, 193 private; 0.5%;
1 of 199 after #171), `ExhaustiveReplay` 1 of 185 (0.5%), `NTimeHierarchy` 1 of 25 (4.0%).
**Cumulative across families** (gate 84's finding 1): after #172, `NTimeHierarchy` carries RS-1's
`un_setup` and TR-1's `nh_accepts_of_halts`, **2 of 25 (8.0%)**. No file reaches one fifth.
**Disposition:** the user's dedup window (12.2c): publish the truncation beside
`FinNDTM.AcceptsWithin.mono` (`ClassNP/NTIME`, which would import `ChoiceWords`; no cycle), and
re-point the three.

**LS-1, the logarithmic bound below the linear one** (PR #175, the move of
`spaceConstructible_poly` to `Constructible`, 2026-10-27, pending its merge; gate 86's pack, item 3).
One fact, `logSpace n ≤ n + 1`, in three places:
- `Machines/ARMWidth`'s public `Complexity.logSpace_le_succ` (line 51), the lemma (a colleague's
  file, outside `Constructible`'s closure);
- `Constructible`'s `spaceConstructible_poly`, the dominance step, inline through `logSpace_eq` and
  `Nat.log_le_self` (before #175 it cited `logSpace_le_succ` from `Savitch`, whose closure has
  `ARMWidth`);
- `Constructible`'s `spaceConstructible_linear`, its dominance conjunct, inline as
  `Nat.succ_le_succ (Nat.log_le_self 2 n)` by reduction of `logSpace` (another file's definition;
  the proof predates rule 10).

Two inline steps and one declaration; the one-fifth rule is not in question. **Accepted (user,
2026-10-27; gate 86's finding 1)** as debt, the new inline step included. **Disposition:** the
user's dedup window (12.2c): move `logSpace_le_succ` into `SpaceComplexity/Basic` beside
`logSpace_eq` (a mechanical edit in `ARMWidth`, FYI to its author), and re-point the two inline
steps to it. **Brought forward (user, 2026-11-04): PR #181** (gate 89) does exactly that, and also
moves `logSpace_le_of_le_mul_two_pow` to `Basic` and `LOGSPACE_subset_PSPACE` and
`SPACE_succ_pow_subset_PSPACE` to `SpaceClasses`. **LS-1 is retired when #181 merges.**
**Scope corrected (gate 89, round 1, major 1).** Two further inline copies predated #181:
- `narm_decides` (`Machines/NARMProof`);
- `narm_logspace_ptm` (`Machines/NARMLogspace`).

Both are `have hLn : logSpace n ≤ n + 1` by `Nat.log_le_self` and `simp only [logSpace]`, in
Hydroxyi's files, and neither was in this entry. Round 2 of #181 (`1d1247a3`) re-points both to
`logSpace_le_succ`, a mechanical ARM dedup edit (FYI). A search of the round-2 head
(`campaign/gates/89-space-facts-api/evidence/round2/ls1-search/`) finds the fact stated only in
`Basic` and cited everywhere else.
**Scope corrected again (gate 89, round 2, major 1).** Two more inner steps derived the logarithm's
form of the fact, `Nat.log 2 m + 1 ≤ m + 1`:
- `ImplicitlyLogspaceComputable.computesInSpace` (`ImplicitPoly`, Hydroxyi's ARM-program file):
  `W ≤ F + 2` with `W = Nat.log 2 (F + 1) + 1`;
- `mem_LOGSPACE_preimage` (`Logspace/PreimageHost`, the campaign's).

Round 2's search had classed both as "polylogarithmic bounds": true of the enclosing bounds, not of
these steps. Round 3 of #181 (`8d41671c`) re-points both to `logSpace_le_succ` through
`logSpace_eq`. Its exhaustive classification of every `Nat.log_le_self` use and every
`logSpace`-by-successor statement
(`campaign/gates/89-space-facts-api/evidence/round3/ls1-search/classification.md`) finds the fact
proved once, in `Basic`, and cited at eight sites.
**Scope corrected a third time (gate 89, round 3, major 1).** Round 3's search had looked for
`Nat.log_le_self` only, so it missed one more inline copy: `arm_decides` (`Machines/ARMProof`,
Hydroxyi's) proved `hLn : Ls ≤ n + 1`, with `Ls := logSpace n`, by unfolding `logSpace` and citing
`Nat.log_lt_self`. Round 4 of #181 (`a7c2a655`) re-points it to `logSpace_le_succ` (a mechanical ARM
dedup edit, FYI). Round 4's search covers every line that touches `logSpace`'s definition and every
Mathlib upper bound of `Nat.log`
(`campaign/gates/89-space-facts-api/evidence/round4/ls1-search/classification.md`). It finds the
fact proved once, in `Basic`, and cited at nine sites.

**LS-2, the logarithmic bound by the binary length** (gate 89, round 4's search; ruled with it, user,
2026-11-04: "Fix in #181 now"). The fact is `logSpace n ≤ Nat.size n + 1`, equivalently
`≤ |bits n| + 1`; its converse is `|bits n| ≤ Nat.log 2 n + 1`. Before round 4:
- the public `Complexity.LogProg.ISCount.logSpace_le_size_succ` (`Logspace/ISCountMath`);
- inline re-derivations in `Randomized/BPLInP`, twice (`two_pow_codes_le`, `BPL_subset_P`);
- the public `Randomized.PolyAmp.logSpace_le_ell` (`Randomized/SpaceAmplifyPoly`, its `ell n` is
  `|bits n| + 1`), re-proved through `Nat.log_lt_of_lt_pow`;
- the converse, published as `LogProg.length_bits_le_log` (`Machines/Bin`) and re-derived by the
  private `size_le_logSpace` (`Logspace/ISCountGenCorrect`).

All in Hydroxyi's files. `BPLInP` did not import `ISCountMath`. **Retired by #181, round 4**
(`fe4bdb67`, `227d92ee`): `logSpace_le_size_succ` moves verbatim to `SpaceComplexity/Basic` as
`Complexity.logSpace_le_size_succ`, and the four re-derivations cite it or `length_bits_le_log`
(copy deletions and re-points, FYI). Same round, same ruling: `ExpBFS/Run`'s `setup_run` cites its
own file's `lgv_le_succ` for `hv |x| ≤ |x|` instead of re-deriving it (`252bbcb8`).

**LS-3, the binary length as the logarithm** (gate 89, round 4's search). The fact is
`|bits n| = Nat.log 2 n + 1` for `n ≠ 0`. No public lemma states it. Private copies:
- `Constructible`'s `b3a_bits_length` (the campaign's);
- `Randomized/QuasiPolyHierarchy`'s `length_bits_eq` (Hydroxyi's);
- `Diagonalization/NTimeDiagonalizer`'s `qy_log_bits`, with `Nat.size n = Nat.log 2 n + 1` also
  inline in its `qy_two_pow_bits_le` (E-D's file, in flight).

**Census** (gate 89, round 4's minor 2; members over all declarations, private included):
- `Constructible` 1/28;
- `QuasiPolyHierarchy` 1/25;
- `NTimeDiagonalizer` 2/236 (`qy_log_bits` and `qy_two_pow_bits_le`'s inline equality).

None reaches one fifth. The halves of these equalities also prove LS-2's converse
(`QuasiPolyHierarchy:63`, `NTimeDiagonalizer:430`, `:446`); they stay within LS-3, and the one
public converse lemma is `LogProg.length_bits_le_log`. **Accepted (user, 2026-11-04)** as debt.
**Disposition:** the dedup window (12.2c): publish the equality beside `LogProg.length_bits_le_log`
and re-point all four occurrences (the three privates and the inline step) after E-D lands.

**BL-1, elementary bounds on the binary length** (gate 89, round 4's binary-length sweep,
`campaign/gates/89-space-facts-api/evidence/round4/ls1-search/bitsweep.tsv`). One- and two-line
steps that carry a Mathlib `Nat.size` fact over to `|Nat.bits n|` through `Nat.size_eq_bits_len`,
where a lemma already states the bound:
- (i) `|bits n| ≤ m` from `n < 2 ^ m` (`LogProg.length_bits_le`, `Machines/Bin`): `Meyer:189`,
  `MeyerTableau:437`, `ISCountGenCorrect`'s private `bits_succ_le` (`:210`);
- (ii) monotonicity (`LogProg.length_bits_mono`): `NTimeDiagonalizer`'s private `qy_bits_len_mono`,
  `RecordTable:2762`, `InputLength:418`, `:420`, `Catalog:4125`;
- (iii) `|bits n| ≤ n` (`Turing.length_bits_le_self`, `TuringMachine/Encoding`):
  `CodeSimulator:1448`, `NTimeDiagonalizer:455`, `SpaceAmplifyPoly:287` (`ell_le`),
  `RecordTable:2764`, `:4256`;
- (iv) `n < 2 ^ |bits n|`: public as `Randomized.PolyAmp.lt_two_pow_bits` and, for `posWidth`,
  `Turing.record_pos_lt`; inline or private in `NTimeDiagonalizer`'s `qy_lt_two_pow_bits`,
  `Logspace/Mult:254`, `:255`, `WindowClock:119`;
- (v) `2 ^ |bits n| ≤ 2n` or `2n + 1`: public as `Complexity.Codec.two_pow_bits_le` (`Codec/Layout`)
  and `Randomized.PolyAmp.two_pow_bits_le`; inline or private in `Codec/Parse:90`,
  `NTimeDiagonalizer`'s `qy_two_pow_bits_le`, `BPLInP:399`.

The files are the campaign's, Hydroxyi's, E-D's in-flight `NTimeDiagonalizer` and the
colleague-owned `CircuitComplexity/Meyer*`. `Machines/Bin` sits above the `CircuitComplexity` and
`TuringMachine` layers, so several sites cannot import it. Each site is one step, so the one-fifth
rule is not in question. **Accepted (user, 2026-11-04)** as debt. **Disposition:** the dedup window
(12.2c): one home for the five bounds below both layers (beside `Turing.length_bits_le_self`), then
re-points where the imports allow. `CircuitComplexity` needs its own authorization.
**Scope corrected (gate 89, round 4, major 1).** The list above missed:
- `Codec/Layout`'s `wP_le` (iii, through logarithms);
- `PathHard`'s `two_pow_ell_le` (v) and `ell_mono` (ii);
- `RandomWalkPad`'s `padDegree_le` (v);
- `PrimeFind:204`, `:318` and `TQBFHardParams`' `wP_le` (iii).

With `Layout`'s `wP_le`, `Layout` stood at 2 of 9 declarations. **Ruled (user, 2026-11-04): "Re-point
now in #181."** Round 5 of #181 (`d789d6db`, `98912ab2`) re-points every site whose file can reach
a canonical lemma:
- (v) `two_pow_bits_le` moves from `Codec/Layout` to `Machines/Bin`. `Parse:90`, `PathHard`'s
  `two_pow_ell_le`, `RandomWalkPad`'s `padDegree_le`, `BPLInP:399` and `PolyAmp.two_pow_bits_le`
  cite it;
- (iii) `Layout`'s `wP_le` cites `Turing.length_bits_le_self` through the new `Codec.wP_eq`, and
  `TQBFHardParams`' `wP_le`, a restatement of `Codec.wP_le`, is removed. `PrimeFind:204`, `:318`,
  `CodeSimulator:1448`, `RecordTable:2764`, `:4256` and `SpaceAmplifyPoly`'s `ell_le` cite
  `length_bits_le_self`;
- (i) `ISCountGenCorrect`'s `bits_succ_le` cites `length_bits_le`;
- (ii) `PathHard`'s `ell_mono` cites `length_bits_mono`;
- (iv) `WindowClock:119` cites `record_pos_lt`.

`Layout` now has no member. **The residual**, every member of the sweep's classification at
#181's round-5 head (`campaign/gates/89-space-facts-api/evidence/round5/ls1-search/bitsweep-classes.md`):
- (i) `Meyer:189` and `MeyerTableau:437`: colleague-owned `CircuitComplexity`;
- (ii) `RecordTable:2762`, `InputLength:418`, `:420` and `Catalog:4125`: `Machines/Bin` is above
  these files;
- (iv) `Mult:254`, `:255`: no (iv) lemma that this file can reach. `PolyAmp.lt_two_pow_bits` and
  `Turing.record_pos_lt` are two public statements of (iv) in different layers and forms;
- `NTimeDiagonalizer`, E-D's file in flight:
  - (ii) `qy_bits_len_mono`;
  - (iii) `qy_call_bound:455`, which E-D's landing already re-points;
  - (iv) `qy_lt_two_pow_bits`;
  - (v) `qy_two_pow_bits_le`;
  - (iv) **`qy_ones_ge:415–417`, new in round 5's sweep** (two inline `Nat.lt_size_self` steps); **acknowledged (user, 2026-11-04)**. The acknowledgment was asked on the
    premise that E-D's landing re-points it. That premise was wrong: the file does not reach `Machines/Bin`,
    so its disposition is the dedup window.

**Disposition of the residual:**
- E-D's landing PR re-points `qy_call_bound:455` (iii), since the file reaches `Encoding`;
- `NTimeDiagonalizer`'s other four members cannot reach `Machines/Bin`, like `RecordTable`'s, and go
  to the dedup window with the rest;
- `CircuitComplexity` comes under its own authorization.

**Scope by kind (gate 89, round 5, majors 1 and 2; ruled by the user, 2026-11-04: "Acknowledge,
scope by kind").** BL-1's acknowledged scope is every re-derivation of kinds (i)–(vi) anywhere in
TCSlib, whether or not a sweep lists it. A member found later is an accounting correction (a minor,
TEMPLATE failure mode 5), unless it pushes a file past one fifth. The kinds are:
- (i)–(v), above;
- **(vi)**, new: the word-value bound `bitsVal w < 2 ^ |w|` (`LogProg.bitsVal_lt_two_pow`,
  `Machines/Bin`).

Round 5's audit found five members outside the site lists, all predating #181 and all acknowledged:
- (v) `Logspace/QueryReshape`'s private `query_index_bound` (sweep group 90) and
  `Randomized/UniformSample`'s `le_two_pow_size_pred` (group 62), whose positive branches derive
  `2 ^ size n ≤ 2n` natively. Both files reach `Machines/Bin`. `UniformSample` is Hydroxyi's;
- (i) `CookLevin/Hardness`'s private `clCount_width`, by binary induction, and (iii) its
  `clElapsed_width`, through `clCount_width`. `Hardness` reaches `Encoding` but not `Bin`;
- (vi) `Codec/Word`'s `Complexity.Codec.bitsVal_lt_two_pow`, an exact copy of `Bin`'s, which
  `Word` imports. `Word` is Hydroxyi's. Its users would resolve to `Bin`'s through `open LogProg`.

**Census:**
- `QueryReshape` 1/120, `UniformSample` 1/19, `Hardness` 2/545, `Word` 1/47;
- `Bin`'s five members (`length_bits_le`, `length_bits_mono`, `two_pow_bits_le`,
  `length_bits_le_log`, `bitsVal_lt_two_pow`) are the canonical statements the copies re-point to,
  not copies. That makes 5/15, recorded as the one-fifth review item.

**Disposition:** the dedup window, with the rest. The one home below both layers re-points them
once.

**CL-1, the codec languages' sibling idiom** (gate 91, the edge-mode PR's screen; ruled with it,
user, 2026-11-04). Each code language of `SpaceComplexity/Codec` has its own definition, its own
membership lemma at an encoded input (`mem_validLang`, …), its own characterization through the
word-level check (`validLang_iff`, …) and its own decider proof (`validLang_mem`, …). The proofs
repeat two pieces: the decoding of `⟨x, ⟨bits c, bits s⟩⟩` (`pairEncode_inj` twice, then
`bits_injective`) and the decider wrapper (`arm_decides_poly` on `CA`, the `one_run` case split and
the reject branch). The four languages `validLang`, `initLang`, `acceptLang` and `stepLang`
(Hydroxyi's) already formed 31 copy pairs at the base. The edge-mode PR adds `edgeLang`,
`mem_edgeLang`, `edgeLang_iff` and `edgeLang_mem`, 25 more pairs. About 25 lines of shared text
are the decoding proofs and the wrapper's skeleton. The edge mode's own correctness proof
(`edge_round`, `edge_loop`, `edge_tail`) is in no pair. **Census** (gate 91, minor 3; members of the
family over all declarations, private included): `Langs` 8/9 → 10/12, `Checks` 4/26 → 5/31,
`Deciders` 3/16 → 4/22. `Langs` was already above one fifth at the base, from the four existing
languages; the acceptance above covers it. The edge member crosses no new file's threshold.
**Accepted (user, 2026-11-04)** as debt. **Disposition:** the dedup window (12.2c): one membership
lemma for languages of encoded triples, and one decider wrapper parameterized by the mode's tail,
with the five languages re-proved through them. This reworks Hydroxyi's proved deciders, interface
design that waits for him. **Ruled (the user, 2026-11-06; Hydroxyi not active): the full refactor.**

**RO-1, the one-step identity `M.runFrom c 1 = M.step c`** (PR #176, E-Q cont1's landing,
2026-10-27; its review's F5; ruled with the landing, user, 2026-10-27). No public lemma states it
(`MultiTapeTM.runFrom` is in the vendored `Deterministic`). Private copies: `NTimeDiagonalizer`'s
`qy_run_one` (new), `ExhaustiveReplay`'s `xr_runFrom_one`, `SAT`'s `satRed_one`, `CfgRecord`'s
`recordStep_runFrom_one`; inline in 13 declarations (`SeamLayout` 3, `Catalog` 4, `Primitives` 4,
`Loop` 1, `Encoding` 1). Census (declaration members, at #176's head): `NTimeDiagonalizer` 1 of 236
(0.4%), `ExhaustiveReplay` 1 of 185 (0.5%), `SAT` 1 of 270 (0.4%), `CfgRecord` 1 of 138 (0.7%),
`SeamLayout` 3 of 36 (8.3%), `Catalog` 4 of 505, `Primitives` 4 of 285, `Loop` 1 of 205, `Encoding`
1 of 61. The one-fifth rule is not reached. **Disposition:** the dedup window (12.2c): a public
`MultiTapeTM.runFrom_one` in a non-vendored module, and the 17 sites re-pointed.
**+1 (G5's landing, #211; gate 102):** `Robustness/TwoTapes`' `tt_round` closes the one-step
identity inline (`runFrom_succ_eq_step.trans runFrom_zero`), 1 of 104 declarations; 18 sites for
the window.
**The window's first pass (2026-11-06; branch `lean/dedup-ro1` at `7c940a8a`, pushed, no PR):**
`Turing.MultiTapeTM.runFrom_one` in `TuringMachine/CfgFacts` (the user's ruling), the four
privates deleted and the 13 inline sites re-pointed; every changed file elaborates. **The scope is
far larger than recorded**, and the PR is parked for the user:
- a public Bool-only copy already exists: `Turing.runFrom_one` (`Build/EmitIterEmbed:261`,
  `simp [MultiTapeTM.runFrom]`), used four times by `EmitIterBody`;
- the rewrite chain `runFrom_succ_eq_step` + `runFrom_zero` (mostly induction base cases) appears
  in about 186 further declarations in 41 files, among them `Catalog` 26, `Primitives` 23,
  `CookLevin/Hardness` 14, `SAT` 12, `Universal` 12, `Nondeterminism` 10, `EXP` 7, and several
  colleague-owned `CircuitComplexity`/`Meyer` files;
- `have`/`show`/`change` forms: `EmitIterBody`'s `hone`/`honeG`, `NDNormalForm:1766`,
  `NDCodeSimulator:632`, `Primitives`' `splitSafe_one` and `hdepart`, `Catalog`'s
  `f2_splitSafe_one`, `hdepart`, `hfirst`, `Loop`'s `hfirst` and `hs`; and fixed-machine
  statements in `CodeSimulator`, `InputWindow` (`iw_one`), `UniversalK`, `WindowClock`,
  `Inclusions`, `CircuitSatReductionMachine`, `Universal` and `UniversalBlock`.
The ledger's census undercounts accordingly. **Questions for the user:** whether the general
lemma replaces `EmitIterEmbed`'s public `Turing.runFrom_one` (a public removal); and the scope of
the re-points (all non-colleague sites in one PR or several; `CircuitComplexity` needs its own
authorization).

**NB-1, the `Nat.bits` arithmetic family** (PR #176; the review's F2). `NTimeDiagonalizer`'s
`qy_two_pow_bits_le` (the statement of `SpaceAmplifyPoly`'s `two_pow_bits_le`, on `main`) and
`qy_log_bits` (whose `≤` half is `Machines/Bin`'s `length_bits_le_log`); before E3 also
`qy_bits_len_mono` (`Bin`'s `length_bits_mono`) and `qy_lt_two_pow_bits`, now through Mathlib's
`Nat.size` facts; and, inline, `qy_call_bound`'s `(Nat.bits (f a)).length ≤ f a`, the statement of
`Encoding`'s `Turing.length_bits_le_self` (gate 87's finding 2). Census, source-inclusive (gate 87's
finding 3; declaration members, inline steps counted as in RO-1): `NTimeDiagonalizer` 3 of 236
(1.3%), `Machines/Bin` 2 of 12 (16.7%), `SpaceAmplifyPoly` 1 of 20 (5%; `two_pow_bits_le`, on `main`
and on the campaign since its merge of `main`), `Encoding` 1 of 61 (1.6%; `length_bits_le_self`);
the last three are the public originals. Below one fifth. **Disposition:** `qy_call_bound`'s step
re-points to `length_bits_le_self` in E-D's landing (ruled, user, 2026-11-04); the rest in the dedup
window: a shared `Nat.bits` module.

**Cumulative per-file accounting for RO-1 and NB-1** (source-inclusive; gate 87's finding 3).
`NTimeDiagonalizer` 4 of 236 (1.7%: RO-1 1, NB-1 3; 3 after E-D's landing re-points
`qy_call_bound`); `Encoding` 2 of 61 (3.3%: RO-1 1, NB-1 1). Every other file is in one of the two
families only, its census above. No file approaches one fifth.

**RC-1, row candidates from E-Q cont1** (PR #176; the brief's and the report's, the review's F9).
Private leaves and lemmas with no published counterpart, each a candidate public row: the clocked
install call (`QyClockSpec`, `qy_clocked_call`, `qy_clockHost_*`); the framed length comparison
with verdict (`qyCmpTM`, `qy_cmp_run`); the repeating emitter (`qyEmitTM`, `qy_emit_run`,
`qy_emit_stop`); the phase host's segment forms (`qy_hosted*`, `qy_round_of_seg`); the
`Nat.unpair` successor rule (`qy_unpair_succ_*`). Not copies. **Disposition:** promotion when a
second consumer appears, or in the dedup window.

**QF-1, two in-file factorings** (PR #176; the review's F6). The `copyMapTM`/`transferMapTM`
endpoint conversion and the `clockCfg` field conversion recur in `NTimeDiagonalizer` (pairs at
90–94%, justified as readings of different rows). Optional. **Disposition:** the dedup window.

**RC-2, a framed take-one-cell row** (E-D's brief, 2026-11-04; its review's F1, ruled by the user).
No published row writes a blank at one cell, and every framed row needs blanks at its word's
relative positions `-1` and `|w|`, so a word inside a nonblank block cannot be split off by
published rows. E-D's own leaf `dzTakeTM` (read the cell, blank it, step right) fills the gap,
privately. Not a copy. **Disposition:** promotion to a public framed row when a second consumer
appears, or in the dedup window.

**AS-1, machine-specific step lemmas beside the general ones** (#182, gate 90, 2026-11-04). #182
publishes one step equation per instruction (`Complexity.LogProg.astep_inc` … `astep_jeqSnd`,
`Machines/ARM`). Three older lemmas state a step of one particular machine at one label:
`LogProg.astep_call₁` (`UnaryLogspace`: `astep_call` with `vword_unary₁`), and
`BoolCircuit.AdjScan.astep_hit` and `astep_jeqFst` (`CircuitComplexity/LogspaceUniformScan`). They
are specializations, not copies; the copy-text screen pairs none of them. The last shares its short
name with the general `astep_jeqFst`, and resolves by argument type in its own file, which opens
`Complexity.LogProg`. **Disposition:** in the dedup window (mechanical ARM edits, FYI), re-prove the
three through the general equations, and rename the circuit one if the shared name is unwanted.
**Extended (gate 90, minor 3):** three more specializations of `astep_call`:
- `BoolCircuit.AdjScan.astep_rd` (`LogspaceUniformScan:196`, with `vword_unary₁`);
- `BoolCircuit.AdjWalk.astep_call₁` and `astep_call₂` (`LogspaceUniformWalk:288, 298`, with
  `vword_unary₁` and `vword_unary₂`).

**AS-2, implicit `astep` reductions by unification** (gate 105 round 2, finding 1; **acknowledged,
the user, 2026-11-06**). `AReach.step`/`AHalt.step` leave a premise that starts at `astep`, and a
following `change`/`exact` on the concrete continuation reduces it with no `astep` in the text.
Named members: `Logspace/Mult`'s `mult_row_start`, `mult_contribution`, `mult_inner_loop`,
`mult_outer_loop`, `mult_next_column`, `mult_columns_run` and `mult_last_bit`;
`Logspace/QueryReshape`'s `comp_factor_run`, `comp_valid_inner`, `comp_multiply` and
`comp_separator_run`; and `NARMPSem`'s `PSem.of_areach` (`Function.iterate_fixed rfl` at halted
configurations, inside an exclusion). `Mult` crosses one fifth (13/62). **Resolution:** a census by
an `astep` irreducibility seal over every consumer, with controls, then a re-pointing PR after
#214 merges.

**MT-1, machine instruction tables read across files** (gate 105 round 2, finding 2; **acknowledged,
the user, 2026-11-06**). Consumers read a machine's instruction table (`A`, `CA`, …) by
`show A .l = _ from rfl` or `simp [A]` in files other than the table's home: `TQBFARM/Machine`,
`Logspace/PathHardMachine`, `Codec/Machine`, the SavitchARM, ExpBFS, circuit, `CounterProgSimRun`
and `SpaceAmplifyPolyRun` machines. This predates AS-1. `NARMExample`'s `guessValidA` reduces
`NARM.detPart` and should use `NARM.detPart_det`. **Resolution:** per-label instruction equations
(`A_<label>`) published in each machine's own file and the consumers re-pointed, one PR per machine
directory in the dedup window; colleague files mechanical, with an FYI.

**Widened (gate 105, 2026-11-06):** 181 containing declarations in 40 files (8 excluded as machine comparisons; scope `campaign/items/dedup/as1-SCOPE.md`); **the user ruled: all in #214.** That makes six members. None is a copy: the screen with `LogspaceUniformWalk` added gives
170 → 179 declarations and 46 → 46 pairs, identical
(`campaign/gates/90-arm-embed-api/evidence/round1-fix/`). Same disposition, same window.

**NF-X1, an idiom exclusion** (NF's partial delivery, review F6; ruled by the user, 2026-11-04).
`NTimeHierarchy.lean::un_setup` reproduces 57% of `NDNormalForm.lean::nf_setup`. The shared text
is three invocations of the published initial-configuration field equations
(`MultiTapeTM.initCfg_eq`, `Cfg.init_state`, `Cfg.init_workTapes`): the idiom of reading the
initial configuration, not a re-derived composite. **Disposition:** excluded; not counted.

**E-D's delivery** (`exists_diagonalizer`, #188; review `campaign/fills/eq/reviews/ed-fill/`;
ruled by the user, 2026-11-04):
- **BL-1 (vi):** `dz_word_lt` (`Nat.ofDigits 2 (w.map Bool.toNat) < 2 ^ |w|`) is a new member,
  **acknowledged** for the dedup window's single home below both layers; `NTimeDiagonalizer`
  cannot reach `Machines/Bin`. Census `NTimeDiagonalizer` (vi) 1.
- **Removed at landing:** `dz_padded_value`'s inline re-derivation of Mathlib's
  `Nat.ofDigits_append_replicate_zero` (E3), and `dz_top_run`'s inline first halt, FH-1's
  `MultiTapeTM.exists_first_halt` (E4). Recorded so that the ledger shows them caught.
- **Promotion requests:** `dz_split_stream` restates `Build/NDHost`'s private `guessRun_split`
  (98%), to be promoted or given a public `List` form; `dz_word_lt` restates `ExhaustiveReplay`'s
  private `xr_val_lt` (65%), with BL-1 (vi)'s home.
- **QF-1, extended:** `dz_initCfg` and `qy_initCfg` state one fact for different machines ("a
  phase host's initial configuration is the blank seam in normal form"); one generic lemma over
  `phaseHostTM_q₀` and `initCfg_ofWords`.
- **RC-3, row candidates:** the clocked hosted run (`DzClockSpec`, `dz_clock_exists`); the
  silent-transport reconstruction (`dz_silentCfg_eq`), beside `embedEmitCfg_eq`; and the output
  length of a computed function (`dz_out_le`, `|F y| ≤ T |y|`), also inline in `SAT`,
  `Nondeterminism`, `TMSAT` and `Build/Loop`'s private `loop_fuel_width`. **Disposition:** the
  dedup window.
- **Census, landed (gate 93, finding 4):** 8 of `NTimeDiagonalizer`'s 342 declarations (2.3%),
  deduplicated: RO-1's one, the five distinct NB-1/BL-1/LS-3 members, `dz_word_lt` and
  `dz_split_stream`. E1 retires `qy_call_bound`'s BL-1 (iii) step. Row candidates (RC-3) and
  in-file factorings (QF-1) are not counted as debt.
- **ED-IN, inline re-derivations, scoped by kind (ruled by the user, 2026-11-04, gate 93 round
  2):** any inline step in `NTimeDiagonalizer` that re-derives a published run, buffer or segment
  lemma belongs to this family, for the dedup window; a later find is an accounting minor. The
  members found so far are all removed: `dz_first` (`Segment.time_eq`), `dz_split`'s separator
  (`bufferTape_append_mid`), `dz_split_tape`'s prefix (`bufferTape_take`), `dz_top_run`'s output
  (`runFrom_output_eq_of_halt`), and three natural cells (`bufferTape_nat`).
  **Further member (gate 93 round 3, finding 1):** `qy_patch_end`'s prefix branch re-derives
  `FinTM.bufferTape_take` (and so `_take` has a counterpart, against BW-1's note); re-pointed in the
  dedup window. Census 9 of 342.
- **Removed in round 2 (gate 93, findings 1–2):** `dz_first` re-proved `Segment.time_eq`, and
  `dz_split`'s separator cell re-proved `FinTM.bufferTape_append_mid`. Both now cite them (#188
  `a64f513d`).

**NF cont1's delivery, F2: four kinds re-stated** (review
`campaign/fills/c1/reviews/nf-cont1-fill/`; ruled by the user, 2026-11-04: **publish homes
first**). An API PR publishes each fact beside its definitions before NF lands, and NF's landing
cites them:
- (i) the input read depends on the input head only (`nf_inputSymbol_congr`; privates
  `ExhaustiveReplay.xr_inputSymbol_congr`, `ZoneRebalance.zr_inputSymbol_congr`);
- (ii) a live configuration redirected to `⟨i, q⟩` is phase `i`'s tagged configuration at `q`
  (`nf_retag`; `SeamLayout`'s private `sl_rewrap`, and inline in 15 declarations);
- (iii) a configuration tagged by phase `i` is at no state of another phase (`nf_tagged_ne_park`;
  privates `CfgRecord.record_tag_ne`, `SeamLayout.sl_tagged_ne_done`);
- (vi) the length of a list of equal-length chunks (`nf_stream_length`; public as
  `Complexity.CfgTableau.length_flatMap_const` in colleague-owned `CircuitComplexity`, which
  NF cannot import).

The existing private copies are re-pointed in the API PR where the files are the campaign's.
*Numbering (gate 95, note 9):* the kinds carry the review's labels, (i)–(iii) and (vi), as in the
decision put to the user. This entry first numbered the chunk length (iv), which collided with the
review's F8 (iv), the buffer end (RC-4 below). The review uses no (v).

**RN-1, renamed configurations converted field by field, scoped by kind** (ruled by the user,
2026-11-04, with gate 94). #190 publishes the general fact, `Turing.Cfg.mapState_eq_of_fields`: a
renamed configuration equals any configuration with its data fields and the renamed state.
- **The family:** every inline proof of that fact anywhere in TCSlib (the five-line
  `Cfg.ext`/`Cfg.mapState_*` block), with the retag (ii) as an instance. A later find is an
  accounting minor.
- **Re-pointed in #190:** `CfgRecord`'s `recordStep_mapState_eq` (removed), `SeamLayout`'s
  `sl_rewrap`, and `ExhaustiveReplay`'s `xr_phase_step` (two blocks) and `xr_halt_fixed` (two
  blocks).
- **Remaining, for the dedup window** (gate 94's minors 1–2, 2026-11-05; counted as conversions
  inside declarations, not copies of their statements). By file:
  - `CodeSimulator`: `canonStageLeg0`–`6`, `canonStageOuterSpec`, `canonStageInnerSpec`,
    `us_start` (10);
  - `ZoneRebalance`: 21 of about 870 (2.4%). These are `zr_short_fields`,
    `zr_rightSeekBack_post`, `zr_rightRuler_post`, `zr_adjustedWalk_post`,
    `zr_adjustedBack_post`, `zr_writeHalves_post`, `zr_rightPass_post`, `zr_test_post`,
    `zr_body_post`, `zr_return_post`, `zr_rightReturn_post`, `zr_rightLeft_post`,
    `zr_twoSteps_fields`, `zr_leftMove_fields`, `zr_leftWrite_fields`, `zr_leftPass_fields`,
    `zr_final_fields`, `zr_extend_fields`, `zr_scanBody_fields`, `zr_scan_fields` and
    `zr_countClear_fields`. RI-1's `zr_pinLoop` is retired and not counted;
  - `NDHost`: `gr_handoff`, `guessCtlRunTM_stop_of_halted`;
  - one each in `ExhaustiveReplay` (`xr_E_initCfg`), `NDCodeSimulator`
    (`exists_ndInterpreterCore`), `Seam` (`phaseHostTM_run`), `InputRewind`
    (`Cfg.mapState_mapState`), `NTimeHierarchy` (`un_setup`; NF-X1's pair too) and `SeamLayout`
    (`exists_seamLayoutTM`).
**+6 (gate 109, minor 1):** `SpaceComplexity/Hierarchy` (H's landing, #218): six `Cfg.ext` conversions over `Cfg.mapState` in four privates; re-pointed in #218 (`1a782c36`).

  The NF review's F2 list has 19 names, not 15; its `xr_phase_step` and `xr_halt_fixed` are
  re-pointed. No file crosses one fifth. NF's own copies (`nf_retag`, `nf_tag`, …) are checked at
  NF's landing (#191), where they cite `CfgFacts`.
The 15 inline (ii) steps and `CircuitComplexity`'s lemma go to the dedup window (the latter under
its own authorization). Also removed at NF's landing: `nf_all_cons`'s re-derivation of Mathlib's
`Nat.forall_lt_succ_left'` (E1).

**RN-1, an accounting minor at NF's landing** (gate 95, minor 3; 2026-11-05). `NDNormalForm`'s
`nf_pack` proved its local `hinit`, `(H.relabelState e).initCfg x = (H.initCfg x).mapState e`
(lines 62–69 at #191's head `e8994dc1`), by the five-line block: an RN-1 member that the list
above did not name. It is inside the family, so a minor. #191's repair commit `10c01517` cites
`(Cfg.mapState_eq_of_fields …).symm` there, as `nf_tag` does since `5732d5bd`. The file's other
eleven `Cfg.ext` blocks (`nf_sweep_run`, `nf_entry` and nine leaf-run endpoints) are
configuration-record equations, not renamings, so they are not members. Census: `NDNormalForm`
1 of 104 declarations at `e8994dc1`, none at `10c01517`.

**NF's landing, gate 95's major 1: repaired, no new family** (#191; ruled by the user,
2026-11-05: **repair**). At the landed head `NDNormalForm` imports `TuringMachine/BufferWords`,
but three inline steps still re-proved its identities, outside every acknowledged family (ED-IN
is scoped to `NTimeDiagonalizer`, BW-1 to `StepBlock`'s privates, RN-1 to renamings):
- `nf_bClear`'s `hw`, `bufferTape R (p + i) = bufferTape (R.drop i) p` for `0 ≤ p`, by
  `bufferTape_nat` twice and `List.getElem?_drop`: that is `FinTM.bufferTape_drop`;
- `nf_aReturn`'s `hw` (cell `|s|`) and `nf_region`'s cell `|R|`, blank at the buffer's end by
  `bufferTape_nat` and `List.getElem?_eq_none`: that is `FinTM.bufferTape_eq_none_of_not_mem`.

The steps came from the brief's own route probes, written when the fill could not import
`BufferWords`. #191's repair commit `10c01517` cites the two lemmas at the three sites, and no
member remains. Recorded so that the ledger shows them caught.

**Gate 95's round-2 major 1** (#191; repaired, the round-1 ruling's kind): `nf_split`'s local `h0`
rebuilt a list from its indexed entries by `List.ext_getElem`, re-proving Mathlib's
`List.ofFn_getElem` (with the index length moved by `List.ofFn_congr`). #191's commit `dfc3e990`
cites the two lemmas. No family; recorded so that the ledger shows it caught.

**The library sweep that followed** (gate 95, round 3; `evidence/round3/sweep/`). Every `have`,
`obtain` and private theorem of the file about core or Mathlib objects only, probed by `exact?`
in place, as a generalised `example` and as its normalised core with `apply?`. It found eight
further inline re-proofs, all of one published lemma each:
- `Nat.succ_mod_succ_eq_zero_iff` (`nf_ctl_position`), `Nat.pos_of_mul_pos_left`
  (`nf_display_firstStop`, `nf_firstStop_records`), `Nat.div_lt_of_lt_mul`
  (`nf_display_firstStop`), `Nat.mul_div_cancel'` (`nf_firstStop_records`);
- `List.ofFn_eq_nil_iff` (`nf_split`), `List.ne_nil_of_length_pos` (`nf_V_display`,
  `nf_forward`; the file already cited it twice).

It also found two rewrite chains that are each one lemma: `List.length_take` with
`Nat.min_eq_left` is `List.length_take_of_le` (eight sites), and `List.foldl_append`,
`foldl_cons`, `foldl_nil` on `l ++ [x]` is `List.foldl_concat` (seven sites). Separately,
`nf_prefix_last` and `nf_sweep_record` proved the same completion of the parser's prefix array;
it is now one private, `nf_update_last`. #191's commit `49c4d0f7` repairs all of them, with no
statement change. No family; no member remains.

**Gate 95's round-3 major 1**: one more member, which the sweep's candidate list missed because it
is an untyped `have`. `nf_display_firstStop`'s `he` (`Nat.mod_add_div`, then the zero remainder)
re-proved `Nat.mul_div_cancel'`; #191's commit `698dcdf5` cites it. The sweep now also takes every
untyped `have`/`obtain` on a core or Mathlib term with a later rewrite `at` it (gate 95,
`evidence/round4/sweep/`); the one other such site, `nf_display_flag`'s `hm`, has no library
statement. No family; no member remains.

**Gate 95's round-4 major 1**: one more fold-concatenation member, in `nf_ctl_position`'s
`simp only` set, which the round-3 sweep had wrongly exempted as a simp set. #191's commit
`b4af93b7` cites `List.foldl_concat`. The sweep now checks every member of both chain classes
anywhere in the file (gate 95, `evidence/round5/sweep/`). No family; no member found by that
check.

**RC-4, row candidates from NF cont1** (the cont1 review's F8, 2026-11-04; completed by gate 95's
note 9, 2026-11-05). The review's list "for the ledger" named F8's row candidates; they were not
carried here until now.
- **The first halting time of a choice word**, FH-1's kind for `NDTM.runWith`: `Nat.find` over
  the run's prefixes (`find_spec`, `find_min`, `find_min'`), then the output after the halt by
  `NDTM.runWith_append` and `NDTM.runWith_of_halt`. FH-1's public form,
  `MultiTapeTM.exists_first_halt`, is deterministic, and no `NDTM` form exists. It runs inline at
  two sites: `NDNormalForm`'s `nf_forward` (lines 3097–3127 at #191's head `e8994dc1`) and
  `ExhaustiveReplay`'s `xr_replay_host` (lines 2179–2189 at the campaign tip). Neither
  re-derives a lemma. **Disposition:** a public `NDTM` first-halt row in the dedup window
  (12.2c), cited at both sites.
- **(iv) a buffer is blank at and past its end** is not a row candidate after all: the review's
  "no public form" held only at the fill's frozen imports. `FinTM.bufferTape_eq_none_of_not_mem`
  (`TuringMachine/BufferWords`, public since PR #140; BW-1) states it. NF's three inline sites
  cite it: `nf_entry` since `4354cbeb`, `nf_aReturn` and `nf_region` since `10c01517` (major 1
  above). `CodeSimulator`'s private `canonStageBuffer_none` (lines 5040–5043 at the campaign
  tip; six invocations at five locations: lines 5203, 6422, 6566, 6778 and twice at 7022, corrected
  by gate 95's round-2 minor 3) restates it for cells at or past the end. **Disposition:** the dedup
  window (12.2c): re-point all six invocations to `FinTM.bufferTape_eq_none_of_not_mem` and delete
  it.
  `CodeSimulator` does not import `BufferWords` yet; the import is acyclic (`BufferWords`
  imports only `Simulation`).

Census (members over all declarations, as the style lint counts them, at the campaign tip):
`CodeSimulator` 1 of 208 (`canonStageBuffer_none`). With CC7-1's eleven and RN-1's three others
(`canonStageOuterSpec`, `canonStageInnerSpec`, `us_start`, the last also RS-1's), the file holds
15 of 208 (7.2%). The first-halt sites are row candidates and are not counted, as in RC-1–RC-3.
The one-fifth rule is not reached.

**WS-1, one step keeps a configuration in a window, and window monotonicity, scoped by kind**
(#196, the deepening's API; gate 96, major 2; acknowledged by the user, 2026-11-05, and widened by
kind the same day). #196's public `Turing.Cfg.InWindow.apply_of_lt` (`Build/CfgRecord`)
re-derived its own file's private `recordStep_window` (line 679 at #196's head `89f4ebbc`), and
one of its steps repeated `ExpBFS.inWin_mono`'s second component verbatim. The v3 screen paired
none of them (the proofs are restructured), and no family covered the kind, so it was a debt
major.
- **Ruled (user, 2026-11-05): harvest.** On #196's repaired head `b1b5199b`, `recordStep_window` is
  public as `Turing.Cfg.InWindow.apply_iff`, over any alphabet, beside the new
  `Turing.Cfg.InWindow.mono`; `apply_of_lt` is proved from the two; and the record step
  (`recordStep_observed_action`), the private lemma's one use, cites `apply_iff`.
- **The family, acknowledged by kind for 12.2c (user, 2026-11-05), widened by kind (user,
  2026-11-05):** every proof, anywhere in TCSlib, that one step keeps a configuration within a
  window of any shape (the radius window `Cfg.InWindow`, a per-tape radius, an interval, a
  visited interval), and every proof of window monotonicity. A later find is an accounting minor.
  The canonical statements:
  - `Turing.Cfg.InWindow.apply_iff`: for `c` in the radius-`s` window, `(a.apply c).InWindow s`
    holds iff no work head is at `-s` moving left or at `s` moving right;
  - `Turing.Cfg.InWindow.mono`: `c.InWindow s → s ≤ s' → c.InWindow s'`;
  - **the tape half**, to be published in the 12.2c window: an action changes a work cell only
    under that tape's old head (`z ≠ c.workTapePos i → (a.apply c).workTapes i z =
    c.workTapes i z`). It exists today as `TuringMachine/Oracle`'s private
    `apply_workTapes_eq_of_ne` (line 304 at the campaign tip), the natural one to harvest.
- **Members on `Cfg.InWindow`** (lines at the campaign tip):
  - `Complexity.ExpBFS.inWin_mono` and `inWin_stepWith` (`SpaceComplexity/ExpBFS/Radius`, lines
    63 and 70; Hydroxyi's): the monotonicity, and one choice step from radius `s` into `s + 1`;
  - the window half of `Complexity.Codec.boundary_iff` (`SpaceComplexity/Codec/Step`, line 195;
    Hydroxyi's): once the two boundary cells are read as head conditions, `apply_iff`;
  - `codec_step_blank` (private, `ClassPSPACE/TQBF`, line 1505; the campaign's): the tape half at
    the same radius for one deterministic step;
  - `xr_window_stepWith` (private, `ClassNP/ExhaustiveReplay`, line 67; the campaign's):
    `inWin_stepWith` for any machine, with `Cfg.InWindow`'s two clauses written out (its output
    bound is outside the kind).
- **Members over other window shapes** (the widening; all the campaign's):
  - `Turing.FinTM.source_bounds` (`TuringMachine/Sweep`, line 359): the interval `[-t, t]`, its
    one-step case inline;
  - `Turing.OracleTM.step_radius` (`TuringMachine/Oracle`, line 346): a per-tape radius, one
    oracle step, through the private tape half above;
  - `dgWindow_step` (private, `TuringMachine/Robustness/SingleTape`, line 1933): the window part of
    a grown interval (its visited, history and size fields are outside the kind);
  - `emCall_track_support` with `emCall_track_extent` (private, `TuringMachine/Build/Loop`, lines
    3316 and 3294): the visited interval of a source run, its step inline.
- **Disposition:** the dedup window (12.2c): publish the tape half, then re-prove the members from
  the canonical statements or re-point their uses; a member over another window shape keeps its
  own statement and cites the canonical ones for its step. Eight of the members re-prove the tape
  half.

Census (members over **all source declarations**, public and private, anonymous instances
included, as `devtools/seyoon/declfreeze.py` counts them at #196's repair `b1b5199b`; corrected
by gate 96's round-2 minor 1, which found the style lint's count, without the seven anonymous
private instances, used before): `Build/CfgRecord` 2 of 137 (1.5%; the canonical pair), 3 of 137
(2.2%) with RO-1's `recordStep_runFrom_one`; `ExpBFS/Radius` 2 of 27 (7.4%) for WS-1, and **3 of
27 (11.1%) cumulatively** with CE-1's `coreSum_eq_of_code_eq`; `Codec/Step` 1 of 30 (3.3%); one
member each in `TQBF`, `ExhaustiveReplay`, `Sweep`, `Oracle` (`step_radius`; its private
`apply_workTapes_eq_of_ne` is the tape half's harvest source, not a copy) and
`Robustness/SingleTape`, and two declarations in `Build/Loop`. The one-fifth rule is not
reached.

**WL-1, a `WalkLe` equation in a consumer file** (gate 96, minor 3's residue; recorded
2026-11-05). `Complexity.LogProg.ISCount.walkLe_succ_iff` (`Logspace/ISCountMath`, line 120),
the last-edge form
`WalkLe R K (j + 1) c t ↔ WalkLe R K j c t ∨ ∃ w, WalkLe R K j c w ∧ R w t ∧ t < K`,
is a fact about `Complexity.WalkLe` (`Logspace/PathWalk`) that lives in a consumer file and
namespace, and its proof unfolds `WalkLe` by `simp only [WalkLe]`, a cross-file unfolding.
Since #196's repair (`b1b5199b`) `SavitchARM/Reach` no longer uses it: `chain_of_walkLe` reads
walks at the front through the new `Complexity.walkLe_succ_iff_head` (`PathWalk`, `Iff.rfl`),
and `Reach` imports `PathWalk` instead of `ISCountMath`. Its remaining uses are in
`ISCountMath`'s own `mem_succ_iff`. Not a copy. **Disposition:** the dedup window (12.2c): move
it beside `WalkLe` in `PathWalk`, or re-prove it there from `walkLe_succ_iff_head` without
unfolding, and cite it from `ISCountMath`. Both files are Hydroxyi's. **Ruled (the user, 2026-11-06): move it
to `PathWalk` as `Complexity.walkLe_succ_iff`, after #216 (which removes its unfolding) merges.**

**WC-1, a window-run closure lemma (optional)** (gate 96, note 10; recorded 2026-11-05).
`Complexity.ExpBFS.winRun_of_card_eq` (`ExpBFS/Radius`) and the induction inside
`Complexity.LogProg.SavitchARM.mem_iff_reach_of_noEdge` (`SavitchARM/Window`) share about ten
lines of one skeleton: extend a window run by `WinRun.snoc`, then finish with `rcode_iff` and
`mem_acceptLang`. The closing steps differ: a shared pattern, not a copy. The induction also
shows more than it states: under `NoEdge`, every word is a window run. **Disposition
(optional):** the dedup window (12.2c): one closure lemma, "if every one-step extension of a
window run stays in the window, every word is a window run", from which `winRun_of_card_eq` and
a public `winRun_of_noEdge` both follow.

**QL-X1, an idiom exclusion: the query layout** (gate 96, note 11; ruled by the user,
2026-11-05). `SavitchARM/Window`'s `NoEdge` reproduces 85% of `SavitchARM/Recursion`'s `Rel` on
the v3 screen. The shared text is the query layout
`pairEncode x (pairEncode (bits u) … (bits s))`, through which each predicate reads a code
language or an oracle answer; `NoEdge` restates none of `Rel`'s meaning. **Ruled (user,
2026-11-05): an idiom**, as with NF-X1's. **Disposition:** excluded; not counted.

**CQ-1, codec-level query predicates** (gate 96, note 11; opened by the user, 2026-11-05, as a
12.2c item). The queries "`⟨x, ⟨bits u, bits s⟩⟩` is in `initLang N`" (and likewise for
`acceptLang N` and `edgeLang N`) are spelled out wherever they are used: in
`Complexity.LogProg.SavitchARM`'s `mem_iff_reach` and `NoEdge`, and in the deepening's block-fit
lemmas (the design's `BlockFit` probe: `fit_initO`, `fit_edgeO`, `fit_accO`, `fit_edge_block`).
`Logspace/ISCountGenRadius` names two of them as public `abbrev`s in a consumer file,
`ISGen.InitM` and `ISGen.AccM`, with no `_iff` lemmas. **Disposition:** the dedup window
(12.2c): a `def` per query, each with its `_iff` lemma, beside `initLang`, `acceptLang` and
`edgeLang` (`SpaceComplexity/Codec/Langs`), replacing `ISGen`'s `InitM` and `AccM` and serving
`mem_iff_reach`, `NoEdge` and the fit lemmas alike. `Codec/Langs` and `ISCountGenRadius` are
Hydroxyi's: interface design in their files. **Ruled (the user, 2026-11-06): as disposed, with
`ISGen.InitM`/`AccM` deleted and their uses re-pointed.**

**RP-1, definitional reads that #196's equations can replace** (gate 96, the round-2 shape
search; recorded 2026-11-05; not duplication). #196 publishes `Iff.rfl` equations for `WalkLe`,
`StepRel`, `RCode`, `WinRun`, `Rel`, `InitO` and `AccO`. Colleagues' files read these definitions
by unfolding or by definitional equality: `WalkLe` in `Logspace/ISCountGenWalk` (83–105),
`PathWalkMachine` (429–439) and `ISCountMath` (124); `StepRel` in `ExpBFS/Radius` (167),
`Logspace/PathHard` (232) and `Randomized/BPLInPCount` (119); `RCode` in `ExpBFS/Main` (98–104)
and `ISCountGenRadius` (88–92); `Rel`, `InitO` and `AccO` in `SavitchARM/Correct` (55–71); lines
at the campaign tip. **Disposition:** the dedup window (12.2c): re-point them to the equations.
Not counted.
**Widened and in PR #216** (2026-11-06; gate 107): a scoping pass and an exhaustive irreducibility
probe (52 modules) found 23 public proof bodies in 14 files, including `SavitchARM/Reach`'s
`mem_iff_reach` (probe only); all re-pointed (`f200144b`, `3d0f6ceb`). **Retired: #216 merged 2026-11-06 (`e4e7a419`).**

**CE-1, equal codes of window configurations, copied** (found 2026-11-05 by gate 96's round-2
screen; **acknowledged by the user for 12.2c, 2026-11-05**). `coreSum_eq_of_code_eq` (equal
radius-`s` codes of two configurations in the radius-`s` window give equal vertices) is public, with
the same statement and the same one-line proof through `coreSum_eq_of_cfgWord_eq`, in
`SpaceComplexity/ExpBFS/Radius` (`Complexity.ExpBFS`, line 126 at the campaign tip) and in
`Randomized/BPLInPCount` (`Randomized.BPLInP`, line 106). Both files are Hydroxyi's, and the copy
predates #196. **Disposition:** the dedup window (12.2c): keep `ExpBFS`'s and re-point
`BPLInPCount`'s uses. Census: one declaration in each file.

**ZP-1, the zone row's precondition under a change of state** (#197, G5's consumer API; gate 97,
minor 5; ruled by the user, 2026-11-05). `Turing.zoneRowPre` (`Build/ZoneRebalance`) reads only
the work tapes and work tape `0`'s head, so it holds of a configuration exactly when it holds
after the state is renamed or rebound. No public lemma said so. `Build/ZoneStep` re-derived it
privately (`zs_rowPre_mapState`); G5's controller needs it too (its phase host starts a phase at
`d.mapState (fun _ => s₀)` and returns `post.bindState (red p)`); and `ZoneRebalance` proves it
inline twelve times, unfolding `zoneRowPre` with `funext_iff`, `Cfg.mapState_workTapes` and
`Cfg.mapState_workTapePos`. That is legal in the definition's home, so there is no rule-10 issue.
- **Ruled (user, 2026-11-05): publish** `zoneRowPre_congr` (across state types: equal work tapes
  and equal tape-`0` heads give the same precondition, which covers `mapState` and `bindState`)
  and its corollary `zoneRowPre_mapState_iff`, beside `zoneRowPre`. Done on #197's head
  `20e7fc75`; `ZoneStep` cites them, and its private copy is gone.
- **The twelve inline sites are re-pointed in the 12.2c window** (the same ruling): lines 831,
  884, 906, 1239, 2275, 2301, 2362, 3330, 3354, 3432, 3512 and 3539 at #197's original head
  `0a1b64d5` (each 22 lines lower at `20e7fc75`), one in each of `zr_rightSeekBack_post`,
  `zr_rightSeekBack_ruler_pre`, `zr_rightRuler_pre`, `zr_rightPass_pre`, `zr_rightReturn_pre`,
  `zr_rightReturn_post`, `zr_rightReturn_bounds`, `zr_rightLeft_pre`, `zr_rightLeft_post`,
  `zr_rightLeft_fields`, `zr_extend_pre` and `zr_extend_fields`.
- **Not RN-1, by kind.** RN-1's fact is a configuration equation (`Cfg.mapState_eq_of_fields`: a
  renamed configuration equals any configuration with its data fields and the renamed state),
  and its family is the five-line `Cfg.ext`/`Cfg.mapState_*` block. These twelve prove one
  predicate's invariance under a change of state, with no `Cfg.ext` and no configuration
  equation, so they are this 12.2c item, with `zoneRowPre_congr` and `zoneRowPre_mapState_iff`
  as its canonical statements. (Gate 97's pre-dispatch sweep, `evidence/sweep/README.md`, called
  `zs_rowPre_mapState` "RN-1's kind"; by RN-1's scope it belongs here.)
- **G5 (#211, gate 102; the review's F4):** `TwoTapes` does not cite the pair. Each phase starts at
  a configuration built at the phase's own state type (`tt_cfg_rowPre`), and each endpoint is
  converted by `tt_mapState_eq_cfg` through `zoneRowPre_iff` and RN-1's `Cfg.mapState_eq_of_fields`;
  nothing re-derives the state-independence. Not a member; the maintainer accepts the route.

Census (inline steps inside declarations, counted as RN-1's are; members over all declarations,
as the style lint counts them, at `20e7fc75`): `ZoneRebalance` 14 of 875 (1.6%: the twelve sites
and the canonical pair). Four of the twelve declarations also hold an RN-1 block
(`zr_rightSeekBack_post`, `zr_rightReturn_post`, `zr_rightLeft_post`, `zr_extend_fields`), so with
RN-1's 21 the file holds 31 of 875 (3.5%). The one-fifth rule is not reached.

Any new copy in a future delivery enters through the per-delivery ledger
and the one-fifth escalation rule of `workflow.md` §4.

## ===== campaign/items/dedup/as1-SCOPE.md =====

# AS-1 widened scope: proofs that unfold `astep` to compute one instruction step

Base `1fd7d4ce` (branch `lean/dedup-as1`). Scan of every `.lean` file under `TCSlib/` except
`SpaceComplexity/Machines/ARM.lean` (the equations' home), by containing declaration.

**Forms searched.** `simp`/`simp only`/`simpa`/`simpa only`/`simp_all`/`dsimp`/`simp_rw`/`norm_num`/`aesop`
with `astep` (bare or namespace-qualified, not `astep_*`, not `nastep`/`mstep`) in the lemma list, the
scoped `regs [astep, …]` macros (TQBFARM, SavitchARM, ExpBFS, PathHard: they expand to `simp only`),
the PathHard `stp` macro (its body is `simp only [astep, A, …]`), `unfold`/`delta astep`,
`rw`/`rewrite`/`erw [astep]`, and `show`/`change` lines naming `astep`. Found: only the simp-family,
`regs` and `stp` forms. No `unfold astep`, `delta`, `dsimp [astep]` or `rw [astep]` exists; the two
`show`/`rw` hits (`mrun_eq_arun`, `PSem.of_areach`) state `astep` of an iterate, they do not unfold it.
Sites that compute a step by `rfl`/defeq without naming `astep` are not counted.

**General equations** (`SpaceComplexity/Machines/ARM.lean`, section `Steps`, all with hypothesis
`h : A l = .<ins>` at a live configuration `(some l, v, res)`): `astep_inc`, `astep_dec`, `astep_clr`,
`astep_half`, `astep_jz`, `astep_jodd`, `astep_jeq`, `astep_call`, `astep_ret`, `astep_valP`,
`astep_valQ`, `astep_jeqIn`, `astep_jeqFst`, `astep_jeqSnd` (14). Derived, already through them:
`LogProg.astep_call₁` (UnaryLogspace, `unaryFst`), `BoolCircuit.AdjScan.astep_rd`/`astep_hit`/
`astep_jeqFst`, `BoolCircuit.AdjWalk.astep_call₁`/`astep_call₂`. Call sites also need the `vword_*`
lemmas (`vword_whole₁/₂/₃`, `vword_unary₁/₂`). For NARM/MARM deterministic instructions the step
is `astep (fun _ => i)`, re-pointed with `(A := fun _ => i) rfl`.

**Instruction kinds** in the per-declaration table: exact for the changed rows; for the rest, a
heuristic from the declaration's instruction hypotheses, `vword_*` uses and the labels it names
looked up in its directory's machine tables (may include kinds of labels named but not stepped;
`—` = labels passed by hypothesis or `step_of rfl`, kind per site).

## Totals

- Containing declarations found: **181** in 40 files (583 unfolding sites).
- Excluded (machine comparisons): **8**. In scope (step computations): **173**.
- Re-pointed in this change: **43**. Remaining: **130** (over the ~60 threshold, so Step 2 took the reduced path).

## Per file

| File | containing / total decls | excluded | in scope | changed | remaining |
|---|---|---|---|---|---|
| `CircuitComplexity/LogspaceUniformAdj.lean` | 2 / 16 | 0 | 2 | 0 | 2 |
| `CircuitComplexity/LogspaceUniformExample.lean` | 2 / 11 | 0 | 2 | 0 | 2 |
| `CircuitComplexity/LogspaceUniformScan.lean` | 7 / 39 | 0 | 7 | 0 | 7 |
| `CircuitComplexity/LogspaceUniformWalk.lean` | 7 / 43 | 0 | 7 | 0 | 7 |
| `ClassPSPACE/TQBFARM/Correct.lean` | 2 / 4 | 0 | 2 | 0 | 2 |
| `ClassPSPACE/TQBFARM/Leaf.lean` | 6 / 8 | 0 | 6 | 2 | 4 |
| `ClassPSPACE/TQBFARM/Walk.lean` | 7 / 14 | 0 | 7 | 2 | 5 |
| `Randomized/SpaceAmplifyPolyRun.lean` | 2 / 14 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/Codec/Deciders.lean` | 1 / 22 | 0 | 1 | 0 | 1 |
| `SpaceComplexity/Codec/Engine.lean` | 3 / 6 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/Codec/Layout.lean` | 3 / 8 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/Codec/Layout2.lean` | 2 / 5 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/Codec/StepDecider.lean` | 3 / 8 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/CounterProgSim.lean` | 3 / 25 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/CounterProgSimRun.lean` | 1 / 6 | 0 | 1 | 0 | 1 |
| `SpaceComplexity/ExpBFS/Main.lean` | 2 / 24 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/ExpBFS/Relax.lean` | 3 / 24 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/ExpBFS/Run.lean` | 5 / 40 | 0 | 5 | 0 | 5 |
| `SpaceComplexity/ExpBFS/Search.lean` | 3 / 6 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/Logspace/InputAccess.lean` | 8 / 81 | 0 | 8 | 0 | 8 |
| `SpaceComplexity/Logspace/Mult.lean` | 12 / 62 | 0 | 12 | 1 | 11 |
| `SpaceComplexity/Logspace/PathHardRun.lean` | 1 / 4 | 0 | 1 | 0 | 1 |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | 4 / 14 | 0 | 4 | 0 | 4 |
| `SpaceComplexity/Logspace/QueryReshape.lean` | 19 / 118 | 0 | 19 | 3 | 16 |
| `SpaceComplexity/Machines/ARMLoops.lean` | 6 / 11 | 0 | 6 | 0 | 6 |
| `SpaceComplexity/Machines/ARMProof.lean` | 1 / 25 | 0 | 1 | 1 | 0 |
| `SpaceComplexity/Machines/ARMReach.lean` | 2 / 5 | 2 | 0 | 0 | 0 |
| `SpaceComplexity/Machines/ARMRun.lean` | 1 / 9 | 1 | 0 | 0 | 0 |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | 5 / 20 | 0 | 5 | 0 | 5 |
| `SpaceComplexity/Machines/MARM.lean` | 3 / 27 | 2 | 1 | 1 | 0 |
| `SpaceComplexity/Machines/MARMCompile.lean` | 1 / 27 | 1 | 0 | 0 | 0 |
| `SpaceComplexity/Machines/NARM.lean` | 1 / 36 | 1 | 0 | 0 | 0 |
| `SpaceComplexity/Machines/NARMExample.lean` | 2 / 5 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/Machines/NARMKit.lean` | 17 / 32 | 0 | 17 | 17 | 0 |
| `SpaceComplexity/Machines/NARMPSem.lean` | 17 / 30 | 1 | 16 | 14 | 2 |
| `SpaceComplexity/SavitchARM/Recursion.lean` | 8 / 17 | 0 | 8 | 0 | 8 |
| `SpaceComplexity/SavitchARM/Run.lean` | 2 / 19 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/SavitchARM/Search.lean` | 2 / 18 | 0 | 2 | 0 | 2 |
| `SpaceComplexity/SavitchARM/Setup.lean` | 3 / 5 | 0 | 3 | 0 | 3 |
| `SpaceComplexity/UnaryLogspace.lean` | 2 / 25 | 0 | 2 | 2 | 0 |

(total decls = `theorem`/`lemma`/`def`/`abbrev`/`instance`/`example` in the file.)

## Excluded (not step computations)

| File | Declaration | Why excluded |
|---|---|---|
| `SpaceComplexity/Machines/ARMReach.lean` | `astep_cases` (L53) | statement is about `astep` at an arbitrary label (shape of every step); the case split is over all instruction kinds, no one instruction is computed for a machine |
| `SpaceComplexity/Machines/ARMReach.lean` | `arm_step` (L90) | compiled-machine simulation (ARM vs `armProg`): inverts an abstract step hypothesis `hs` per instruction case to feed the `sim_*` lemmas; compares two machines |
| `SpaceComplexity/Machines/ARMRun.lean` | `arm_run` (L119) | compiled-machine simulation (ARM vs `armProg`), the run analogue of `arm_step`; per-case `simp [astep, hA]` side goals sit inside a machine comparison (each branch would accept `astep_<kind> hA`; listed here for the record, not re-pointed) |
| `SpaceComplexity/Machines/MARM.lean` | `mstep_det` (L146) | compares `mstep` with `astep (A.detPart β)` at a register label (machine comparison, MARM vs its deterministic part) |
| `SpaceComplexity/Machines/MARM.lean` | `mrun_eq_arun` (L251) | transfer of whole runs MARM vs deterministic part; the one inner `simp [astep, hret]` is the detPart answer at a memory label inside the comparison (would accept `astep_ret hret`) |
| `SpaceComplexity/Machines/MARMCompile.lean` | `astep_mdetPart` (L265) | compares the deterministic parts `A.detPart β` and `A.detPart β'` (machine comparison) |
| `SpaceComplexity/Machines/NARM.lean` | `nastep_det` (L130) | compares `nastep` with `astep (A.detPart β)` (machine comparison, NARM vs its deterministic part) |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.of_areach` (L328) | transfer of runs ARM-detPart vs PSem semantics; the `show`/`rw` hits state `astep` of the iterate (no unfold), the inner `simp [astep, NARM.detPart_choose hA]` is the detPart answer at a `choose` label inside the comparison |

## Per declaration

| File | Declaration | sites | instruction kinds | equation(s) | status |
|---|---|---|---|---|---|
| `CircuitComplexity/LogspaceUniformAdj.lean` | `lang_mem` (L118) | 2 | valP | `astep_valP` | remaining |
| `CircuitComplexity/LogspaceUniformAdj.lean` | `walk_lang` (L264) | 2 | ret, valP | `astep_ret`, `astep_valP` | remaining |
| `CircuitComplexity/LogspaceUniformExample.lean` | `loop` (L97) | 2 | call, inc, jeqIn, ret | `astep_call`, `astep_inc`, `astep_jeqIn`, `astep_ret` | remaining |
| `CircuitComplexity/LogspaceUniformExample.lean` | `leLang_mem` (L161) | 2 | call, valP | `astep_call`, `astep_valP` | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `uloop` (L279) | 2 | — | per site | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `argsSkip` (L319) | 4 | — | per site | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `argsEx` (L369) | 3 | inc, jeqFst, jeqSnd, valQ | `astep_inc`, `astep_jeqFst`, `astep_jeqSnd`, `astep_valQ` | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `gateSkip` (L424) | 4 | inc | `astep_inc` | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `hitGate` (L460) | 5 | — | per site | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `nloop` (L564) | 3 | — | per site | remaining |
| `CircuitComplexity/LogspaceUniformScan.lean` | `scan_halts` (L628) | 1 | valP | `astep_valP` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `Em.emit` (L253) | 2 | inc, jeqIn, ret | `astep_inc`, `astep_jeqIn`, `astep_ret` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `uLoop` (L342) | 3 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `aLoop` (L380) | 6 | call, jeq | `astep_call`, `astep_jeq` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `gLoop` (L511) | 1 | call, clr, ret | `astep_call`, `astep_clr`, `astep_ret` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `inLoop` (L585) | 1 | call | `astep_call` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `oLoop` (L618) | 3 | jeq, ret | `astep_jeq`, `astep_ret` | remaining |
| `CircuitComplexity/LogspaceUniformWalk.lean` | `walk_halts` (L655) | 3 | call, ret, valP | `astep_call`, `astep_ret`, `astep_valP` | remaining |
| `ClassPSPACE/TQBFARM/Correct.lean` | `inner_spec` (L67) | 5 | call, clr, dec, jz | `astep_call`, `astep_clr`, `astep_dec`, `astep_jz` | remaining |
| `ClassPSPACE/TQBFARM/Correct.lean` | `truth_mem_PSPACE` (L181) | 3 | inc, jz | `astep_inc`, `astep_jz` | remaining |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `read_t` (L56) | 1 | call | `rw [astep_call hl, vword_whole₁]` | changed |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `read_f` (L66) | 1 | call | `rw [astep_call hl, vword_whole₁]` | changed |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `lc_run` (L101) | 4 | call | `astep_call` | remaining |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `lv_run` (L146) | 6 | call | `astep_call` | remaining |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `lit_run` (L206) | 2 | call, inc | `astep_call`, `astep_inc` | remaining |
| `ClassPSPACE/TQBFARM/Leaf.lean` | `formula_run` (L282) | 4 | call, jz | `astep_call`, `astep_jz` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `len_t` (L57) | 1 | call | `rw [astep_call hl, vword_whole₁]` | changed |
| `ClassPSPACE/TQBFARM/Walk.lean` | `len_f` (L67) | 1 | call | `rw [astep_call hl, vword_whole₁]` | changed |
| `ClassPSPACE/TQBFARM/Walk.lean` | `syn_run` (L81) | 1 | call | `astep_call` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `node_run` (L138) | 1 | call, clr | `astep_call`, `astep_clr` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `push_run` (L158) | 4 | clr | `astep_clr` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `pop_run` (L186) | 5 | jz | `astep_jz` | remaining |
| `ClassPSPACE/TQBFARM/Walk.lean` | `leaf_spec` (L238) | 2 | call | `astep_call` | remaining |
| `Randomized/SpaceAmplifyPolyRun.lean` | `ps_steps` (L113) | 1 | call | `astep_call` | remaining |
| `Randomized/SpaceAmplifyPolyRun.lean` | `ps_runs` (L354) | 1 | call | `astep_call` | remaining |
| `SpaceComplexity/Codec/Deciders.lean` | `init_tail` (L265) | 11 | call, clr, dec, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Codec/Engine.lean` | `scan_loop` (L97) | 4 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Codec/Engine.lean` | `halvCount_loop` (L244) | 4 | half, inc, jz | `astep_half`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Codec/Engine.lean` | `le_loop` (L303) | 6 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Codec/Layout.lean` | `layout_run` (L92) | 7 | call, clr, half, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_half`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Codec/Layout.lean` | `le_phase` (L265) | 1 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/Codec/Layout.lean` | `vscan_run` (L296) | 2 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/Codec/Layout2.lean` | `layout2_run` (L67) | 6 | call, clr, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Codec/Layout2.lean` | `insym_run` (L219) | 11 | call, clr, dec, inc, jeq, jz | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Codec/StepDecider.lean` | `pm_run` (L62) | 13 | dec, inc, jeq, jz | `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Codec/StepDecider.lean` | `z_run` (L138) | 4 | dec, jz | `astep_dec`, `astep_jz` | remaining |
| `SpaceComplexity/Codec/StepDecider.lean` | `step_tail` (L181) | 2 | jeq, jz, ret | `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/CounterProgSim.lean` | `pr_reach` (L260) | 5 | clr, inc, jeq, jeqIn | `astep_clr`, `astep_inc`, `astep_jeq`, `astep_jeqIn` | remaining |
| `SpaceComplexity/CounterProgSim.lean` | `pr_halt` (L303) | 6 | clr, inc, jeq, jeqIn, ret | `astep_clr`, `astep_inc`, `astep_jeq`, `astep_jeqIn`, `astep_ret` | remaining |
| `SpaceComplexity/CounterProgSim.lean` | `sim_step` (L355) | 11 | call, inc, jeqIn, ret | `astep_call`, `astep_inc`, `astep_jeqIn`, `astep_ret` | remaining |
| `SpaceComplexity/CounterProgSimRun.lean` | `UnaryLogspace.counterProg` (L142) | 3 | jeqIn, valP | `astep_jeqIn`, `astep_valP` | remaining |
| `SpaceComplexity/ExpBFS/Main.lean` | `fscan_run` (L127) | 4 | call | `astep_call` | remaining |
| `SpaceComplexity/ExpBFS/Main.lean` | `iter_run` (L270) | 1 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Relax.lean` | `ini_run` (L150) | 4 | call | `astep_call` | remaining |
| `SpaceComplexity/ExpBFS/Relax.lean` | `inner_run` (L229) | 7 | call | `astep_call` | remaining |
| `SpaceComplexity/ExpBFS/Relax.lean` | `outer_run` (L371) | 3 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `wo_run` (L242) | 4 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `wb_run` (L272) | 3 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `lg_run` (L396) | 4 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `setup_run` (L428) | 1 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Run.lean` | `wk_run` (L493) | 3 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Search.lean` | `rounds_run` (L94) | 3 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Search.lean` | `count_run` (L166) | 5 | — | per site | remaining |
| `SpaceComplexity/ExpBFS/Search.lean` | `search_run` (L224) | 1 | inc, jz | `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `inputLength_loop` (L612) | 2 | call, inc | `astep_call`, `astep_inc` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `arm_chain` (L668) | 1 | — | per site | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `alignedPair_loop` (L728) | 6 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `registerCopy_loop` (L903) | 3 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `registerScale_loop` (L939) | 3 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `canonicalTail_loop` (L1023) | 7 | call, half, inc, jeq, jz | `astep_call`, `astep_half`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `boundedDecodeStride_loop` (L1125) | 6 | call, clr, dec, inc, jeq, jz | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/InputAccess.lean` | `indexedSeek_loop` (L1294) | 6 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_contribution` (L602) | 3 | call, dec, inc, jeq | `astep_call`, `astep_dec`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_inner_loop` (L642) | 3 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_outer_loop` (L751) | 3 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_finish` (L858) | 2 | jeq, jz | `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_parity` (L871) | 4 | half, jodd | `astep_half`, `astep_jodd` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_result_read` (L895) | 2 | call, dec, jeq, jodd | `astep_call`, `astep_dec`, `astep_jeq`, `astep_jodd` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_next_column` (L916) | 2 | half, inc, jeq | `astep_half`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_columns_run` (L952) | 3 | clr, dec, jeq, jz | `astep_clr`, `astep_dec`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_last_bit` (L1081) | 4 | call, clr, dec, inc, jeq, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_ret` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_canonical_run` (L1195) | 3 | dec, inc, jeq, jz | `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_sub_two` (L1270) | 2 | dec ×2 | `astep_dec code₀`, `astep_dec code₁` | changed |
| `SpaceComplexity/Logspace/Mult.lean` | `mult_prepare_run` (L1291) | 1 | dec, half, inc, jeq | `astep_dec`, `astep_half`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/PathHardRun.lean` | `setup_run` (L110) | 7 | dec, half, inc, jeq, jz | `astep_dec`, `astep_half`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | `dispatch_halt` (L109) | 30 | call, jz | `astep_call`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | `tail_halt` (L175) | 3 | jz | `astep_jz` | remaining |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | `matrix_halt` (L215) | 1 | — | per site | remaining |
| `SpaceComplexity/Logspace/PathHardWalk.lean` | `walk_halt` (L308) | 11 | — | per site | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_hit` (L421) | 1 | call (bit mode) | `astep_call (show dropARM false .hit = _ from rfl)` | changed |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_tail_decode` (L495) | 2 | call, clr, dec, inc, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_lookup` (L649) | 1 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_decrement_run` (L756) | 1 | dec | `astep_dec` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_z_prepare` (L777) | 1 | clr, dec, inc, jeq | `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_u_prepare` (L808) | 1 | clr, dec, inc, jeq | `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `drop_lookup_prepare` (L842) | 1 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_product` (L1423) | 3 | clr, dec, inc, jeq, jz | `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_multiply` (L1498) | 2 | clr, inc, jeq, jz | `astep_clr`, `astep_inc`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_power_run` (L1583) | 2 | jeq, jz | `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_poly_run` (L1627) | 1 | inc, jeq | `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_length_search` (L1677) | 5 | call, jeq, jz | `astep_call`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_canonical_run` (L1809) | 6 | call, clr, dec, inc, jeq, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_ret` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_outer_prepare` (L1864) | 3 | dec, inc, jeq | `astep_dec`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_outer_decode` (L1933) | 3 | call, clr, dec, inc, jeq, jz, ret | `astep_call`, `astep_clr`, `astep_dec`, `astep_inc`, `astep_jeq`, `astep_jz`, `astep_ret` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_inner_prepare` (L2045) | 3 | clr, half, inc, jeq | `astep_clr`, `astep_half`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_call_return` (L2117) | 1 | call | `rw [astep_call hc, vword_whole₁]` | changed |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_prefix_hit` (L2136) | 1 | half | `astep_half (show compARM C e false .prefixHit = _ from rfl)` | changed |
| `SpaceComplexity/Logspace/QueryReshape.lean` | `comp_separator_run` (L2207) | 6 | clr, inc, jeq | `astep_clr`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `move_run` (L115) | 4 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `move2_run` (L172) | 5 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `dmove_run` (L217) | 5 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `sub_run` (L257) | 4 | dec, jz | `astep_dec`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `halve_run` (L290) | 4 | dec, half, jz | `astep_dec`, `astep_half`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMLoops.lean` | `shl_run` (L360) | 3 | dec, inc, jz | `astep_dec`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMProof.lean` | `AHalt.ret` (L110) | 1 | ret | `astep_ret hA` | changed |
| `SpaceComplexity/Machines/ARMReach.lean` | `astep_cases` (L53) | 4 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/ARMReach.lean` | `arm_step` (L90) | 16 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/ARMRun.lean` | `arm_run` (L119) | 16 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `d1_loop` (L147) | 5 | jz | `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `d2_loop` (L174) | 4 | jz | `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `dbl_loop` (L200) | 3 | jeq, jz | `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `enum_loop` (L230) | 4 | call, jeq | `astep_call`, `astep_jeq` | remaining |
| `SpaceComplexity/Machines/ARMWidthExample.lean` | `searchLang_mem_PSPACE` (L281) | 1 | call, inc, jz | `astep_call`, `astep_inc`, `astep_jz` | remaining |
| `SpaceComplexity/Machines/MARM.lean` | `mstep_det` (L146) | 1 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/MARM.lean` | `MHalt.ret` (L218) | 2 | ret (det part) | `astep_ret (A := fun _ => .ret r) rfl` | changed |
| `SpaceComplexity/Machines/MARM.lean` | `mrun_eq_arun` (L251) | 3 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/MARMCompile.lean` | `astep_mdetPart` (L265) | 1 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/NARM.lean` | `nastep_det` (L130) | 1 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/NARMExample.lean` | `guessValidA_halts` (L57) | 4 | jz, ret, valP | `astep_jz`, `astep_ret`, `astep_valP` | remaining |
| `SpaceComplexity/Machines/NARMExample.lean` | `guessValidA_ans` (L75) | 4 | jz, ret, valP | `astep_jz`, `astep_ret`, `astep_valP` | remaining |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.inc` (L198) | 1 | inc (det part) | `astep_inc (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.clr` (L205) | 1 | clr (det part) | `astep_clr (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.half` (L211) | 1 | half (det part) | `astep_half (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jeq_pos` (L218) | 1 | jeq (det part) | `astep_jeq (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jeq_neg` (L224) | 1 | jeq (det part) | `astep_jeq (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jz_pos` (L230) | 1 | jz (det part) | `astep_jz (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jz_neg` (L236) | 1 | jz (det part) | `astep_jz (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jodd_pos` (L242) | 1 | jodd (det part) | `astep_jodd (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.jodd_neg` (L248) | 1 | jodd (det part) | `astep_jodd (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.call_pos` (L254) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.call_neg` (L261) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_dec` (L268) | 1 | dec (det part) | `astep_dec (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_call₂_pos` (L275) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_call₂_neg` (L283) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_call₃_pos` (L291) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `nsem_call₃_neg` (L300) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMKit.lean` | `NSem.ret` (L309) | 1 | ret (det part) | `astep_ret (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.inc` (L136) | 1 | inc (det part) | `astep_inc (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.clr` (L143) | 1 | clr (det part) | `astep_clr (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.half` (L149) | 1 | half (det part) | `astep_half (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jeq_pos` (L156) | 1 | jeq (det part) | `astep_jeq (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jeq_neg` (L162) | 1 | jeq (det part) | `astep_jeq (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jz_pos` (L168) | 1 | jz (det part) | `astep_jz (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jz_neg` (L174) | 1 | jz (det part) | `astep_jz (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jodd_pos` (L180) | 1 | jodd (det part) | `astep_jodd (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.jodd_neg` (L186) | 1 | jodd (det part) | `astep_jodd (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.call_pos` (L192) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.call_neg` (L199) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.ret` (L206) | 1 | ret (det part) | `astep_ret (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.of_areach` (L328) | 5 | (all, abstract) | — | excluded |
| `SpaceComplexity/Machines/NARMPSem.lean` | `searchUp_run` (L389) | 1 | inc | `astep_inc` | remaining |
| `SpaceComplexity/Machines/NARMPSem.lean` | `searchDown_run` (L420) | 2 | dec | `astep_dec` | remaining |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.call` (L455) | 1 | call (det part) | `astep_call (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/Machines/NARMPSem.lean` | `PSem.dec` (L463) | 1 | dec (det part) | `astep_dec (A := fun _ => <ins>) rfl` in the `simpa only` | changed |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `base_spec` (L149) | 3 | call, jeq, jz | `astep_call`, `astep_jeq`, `astep_jz` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `desc1` (L199) | 6 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `desc2` (L272) | 6 | clr | `astep_clr` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `tail0F` (L335) | 2 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `tail1T` (L359) | 1 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `tail1F` (L379) | 2 | clr, jeq | `astep_clr`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `loop_spec` (L426) | 1 | jeq | `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Recursion.lean` | `call_spec` (L480) | 2 | — | per site | remaining |
| `SpaceComplexity/SavitchARM/Run.lean` | `mulL_run` (L169) | 3 | clr, jz | `astep_clr`, `astep_jz` | remaining |
| `SpaceComplexity/SavitchARM/Run.lean` | `mul_run` (L201) | 1 | — | per site | remaining |
| `SpaceComplexity/SavitchARM/Search.lean` | `outerV_run` (L127) | 8 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Search.lean` | `outerU_run` (L207) | 4 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/SavitchARM/Setup.lean` | `ld_run` (L60) | 2 | jz | `astep_jz` | remaining |
| `SpaceComplexity/SavitchARM/Setup.lean` | `pw_run` (L86) | 3 | jz | `astep_jz` | remaining |
| `SpaceComplexity/SavitchARM/Setup.lean` | `setup_run` (L143) | 4 | call, inc, jeq | `astep_call`, `astep_inc`, `astep_jeq` | remaining |
| `SpaceComplexity/UnaryLogspace.lean` | `loop` (L221) | 5 | jeqIn (cmp, 2 sites), inc (i1, i2, i3) | `astep_jeqIn`, `astep_inc` via `show A .l = _ from rfl` | changed |
| `SpaceComplexity/UnaryLogspace.lean` | `ltLang_mem` (L277) | 3 | valP (start, 3 sites) | `astep_valP` via `show A .start = _ from rfl` | changed |

## Proposed split of the remainder (one PR per directory)

- `SpaceComplexity/Logspace`: 40 declarations, 157 sites (InputAccess.lean 8, Mult.lean 11, PathHardRun.lean 1, PathHardWalk.lean 4, QueryReshape.lean 16)
- `CircuitComplexity`: 18 declarations, 49 sites (LogspaceUniformAdj.lean 2, LogspaceUniformExample.lean 2, LogspaceUniformScan.lean 7, LogspaceUniformWalk.lean 7)
- `SpaceComplexity/Machines`: 15 declarations, 53 sites (ARMLoops.lean 6, ARMWidthExample.lean 5, NARMExample.lean 2, NARMPSem.lean 2)
- `SpaceComplexity/SavitchARM`: 15 declarations, 48 sites (Recursion.lean 8, Run.lean 2, Search.lean 2, Setup.lean 3)
- `SpaceComplexity/ExpBFS`: 13 declarations, 43 sites (Main.lean 2, Relax.lean 3, Run.lean 5, Search.lean 3)
- `SpaceComplexity/Codec`: 12 declarations, 71 sites (Deciders.lean 1, Engine.lean 3, Layout.lean 3, Layout2.lean 2, StepDecider.lean 3)
- `ClassPSPACE/TQBFARM`: 11 declarations, 37 sites (Correct.lean 2, Leaf.lean 4, Walk.lean 5)
- `SpaceComplexity`: 4 declarations, 25 sites (CounterProgSim.lean 3, CounterProgSimRun.lean 1)
- `Randomized`: 2 declarations, 2 sites (SpaceAmplifyPolyRun.lean 2)

The `SpaceComplexity/Machines` remainder is `ARMLoops` (6 generic loop runs, hypotheses `hA`),
`ARMWidthExample` (5), `NARMExample` (2) and `NARMPSem.searchUp_run`/`searchDown_run`; the
`Logspace` remainder includes the PathHard `stp` macro, whose body itself unfolds `astep`
(re-pointing its 5 using declarations means replacing the macro's `astep, A` by per-site equations).

## Landed on `lean/dedup-as1` (local, not pushed)

- `1856e771` TQBFARM: `read_t`, `read_f`, `len_t`, `len_f`.
- `5fdcfcf4` SpaceComplexity: `LtM.loop`, `ltLang_mem`.
- `090fcccd` Machines: `AHalt.ret`, `MHalt.ret`, 17 `NSem`/`nsem_*`, 14 `PSem.*`.
- `29c41e09` Logspace: `comp_call_return`, `drop_hit`, `comp_prefix_hit`, `mult_sub_two`.

## ===== campaign/gates/105-as1-dedup/evidence/round2/astep-residual.txt =====

TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean:434:step equations of `astep` and the published loop runs, without unfolding `CA` or `astep`. -/
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:58:  | ret b => exact Or.inr ⟨b, by simp [astep, hA]⟩
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:59:  | valP r l' => by_cases h : ValidPlain x <;> simp [astep, hA, h]
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:60:  | valQ r l' => by_cases h : ValidPair x <;> simp [astep, hA, h]
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:61:  | _ => simp [astep, hA]
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:108:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:112:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:116:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:120:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:124:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:128:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:133:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:138:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:143:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:148:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:151:  | ret b' => simp [astep, hA] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:154:    · simp only [astep, hA, hv, if_true, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:157:    · simp [astep, hA, hv] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:160:    · simp only [astep, hA, hv, if_true, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:163:    · simp [astep, hA, hv] at hs
TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean:169:    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean:151:  simp only [mstep, hA, astep, MARM.detPart_det hA β]
TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean:270:  simp only [astep, MARM.detPart_det hA]
TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean:133:  simp only [nastep, hA, astep, NARM.detPart_det hA β]
TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean:361:              · rw [e] at h; rw [show ((astep (A.detPart false) oracle x)^[n] (none, v₀, some b))
TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean:379:      · rw [he, show ((astep (A.detPart false) oracle x)^[T] (none, v, some b)) = (none, v, some b)

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multiplication in logarithmic space

[AB09, Example 4.7], second language: `MULT = {⟨n, m, nm⟩}` is in `L` by the
grade-school method. Deferred from phase P4.1 to P4.4
(`AroraBarakChapters3-4Plan.md`) for the number-triple encoding conventions,
which the logspace phase fixes: binary components in nested aligned pairs,
little-endian (`Nat.bits`), membership by existential witness over genuine
encodings — the same pattern as `Complexity.PATH`'s instance encoding.

## Main definitions

* `Complexity.multLang` — the triples `⟨a, b, a·b⟩`. [AB09, Example 4.7]

## Main results (proved; phase-P4.4 statement)

* `Complexity.multLang_mem_LOGSPACE` — grade-school multiplication runs in
  logarithmic space. [AB09, Example 4.7]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, Example 4.7.)
-/

namespace Complexity

open Turing

/-- **The language `MULT`** [AB09, Example 4.7]: encodings of triples
`⟨a, b, a·b⟩`, components in little-endian binary, nested aligned pairs.
Strings encoding no such triple are not members. -/
def multLang : Language Bool :=
  {z | ∃ a b : ℕ,
    z = pairEncode (Nat.bits a) (pairEncode (Nat.bits b) (Nat.bits (a * b)))}

/-! ## Private multiplication construction (B7 target 12) -/

open LogProg
open scoped BigOperators

/-- The grade-school column sum, with absent operand bits read as zero. -/
private def multColumn (a b : List Bool) (j : ℕ) : ℕ :=
  ∑ p ∈ Finset.range a.length,
    if p ≤ j then (a.getD p false).toNat * (b.getD (j - p) false).toNat else 0

private lemma multColumn_nil (b : List Bool) (j : ℕ) : multColumn [] b j = 0 := by
  simp [multColumn]

private lemma multColumn_cons (t : Bool) (a b : List Bool) (j : ℕ) :
    multColumn (t :: a) b j = t.toNat * (b.getD j false).toNat +
      match j with
      | 0 => 0
      | k + 1 => multColumn a b k := by
  unfold multColumn
  rw [List.length_cons, Finset.sum_range_succ']
  cases j <;> simp [Nat.succ_sub_succ_eq_sub,
    Nat.add_comm]

/-- Every column has at most one contribution per bit of the first operand. -/
private lemma multColumn_le (a b : List Bool) (j : ℕ) : multColumn a b j ≤ a.length := by
  unfold multColumn
  calc
    _ ≤ ∑ _p ∈ Finset.range a.length, 1 := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · cases a.getD p false <;> cases b.getD (j-p) false <;> decide
      · omega
    _ = a.length := by simp

/-- A weighted prefix of zero-padded bits is the value of the corresponding word prefix. -/
private lemma mult_bits_prefix (w : List Bool) (n : ℕ) :
    (∑ j ∈ Finset.range n, 2 ^ j * (w.getD j false).toNat) = bitsVal (w.take n) := by
  induction n generalizing w with
  | zero => simp [bitsVal]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    cases w with
    | nil => simp [bitsVal, List.getD_eq_getElem?_getD]
    | cons t w =>
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul,
        List.take_succ_cons, bitsVal, pow_succ]
      calc
        _ = 2 * (∑ j ∈ Finset.range n, 2 ^ j * (w.getD j false).toNat) + t.toNat := by
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [ih]; omega

/-- Splitting off the low bit splits the convolution into a scalar row and a shifted product.
Proof sketch. Expand both prefixes at their first term and distribute the finite sums. -/
private lemma mult_column_prefix_cons (t : Bool) (a b : List Bool) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), 2 ^ j * multColumn (t :: a) b j) =
      t.toNat * bitsVal (b.take (n + 1)) +
        2 * (∑ j ∈ Finset.range n, 2 ^ j * multColumn a b j) := by
  rw [← mult_bits_prefix b (n + 1)]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [multColumn_cons, pow_zero, one_mul, Nat.add_zero]
  simp_rw [pow_succ, Nat.mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have h₁ : (∑ j ∈ Finset.range n, 2 ^ j * 2 *
      (t.toNat * (b.getD (j + 1) false).toNat)) =
      ∑ j ∈ Finset.range n, t.toNat * (2 ^ j * 2 * (b.getD (j + 1) false).toNat) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h₂ : (∑ j ∈ Finset.range n, 2 ^ j * 2 * multColumn a b j) =
      ∑ j ∈ Finset.range n, 2 * (2 ^ j * multColumn a b j) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [h₁, h₂]
  ring

/-- Once all possible columns are included, their weighted sum is the product.
Proof sketch. Induct on the first operand, using the preceding convolution decomposition
and the received definition of `bitsVal`; the length bound removes the second-word take. -/
private lemma mult_columns_value (a b : List Bool) (n : ℕ)
    (hn : a.length + b.length ≤ n) :
    (∑ j ∈ Finset.range n, 2 ^ j * multColumn a b j) = bitsVal a * bitsVal b := by
  induction a generalizing n with
  | nil => simp [multColumn_nil, bitsVal]
  | cons t a ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      rw [mult_column_prefix_cons, List.take_of_length_le (by simp only [List.length_cons] at hn; omega),
        ih n (by simp only [List.length_cons] at hn; omega)]
      simp only [bitsVal]
      ring

/-- Carry entering a column; it starts at zero and is halved after the column is added. -/
private def multCarry (a b : List Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (multCarry a b j + multColumn a b j) / 2

/-- The carry never exceeds the first operand's bit length. -/
private lemma multCarry_le (a b : List Bool) (j : ℕ) : multCarry a b j ≤ a.length := by
  induction j with
  | zero => simp [multCarry]
  | succ j ih =>
    have hc := multColumn_le a b j
    simp only [multCarry]
    omega

/-- The exact column/carry invariant of [AB09, Example 4.7] (P4.4 audit, Q8).
Proof sketch. Add the next weighted column to the induction hypothesis. Euclidean
division splits the new accumulator into its parity and twice the next carry. -/
private lemma mult_carry_invariant (a b : List Bool) (n : ℕ) :
    (∑ j ∈ Finset.range n, 2 ^ j * multColumn a b j) =
      (∑ j ∈ Finset.range n,
        2 ^ j * ((multCarry a b j + multColumn a b j) % 2)) +
      2 ^ n * multCarry a b n := by
  induction n with
  | zero => simp [multCarry]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ, multCarry]
    have hd := Nat.mod_add_div (multCarry a b n + multColumn a b n) 2
    have he := congrArg (fun k => 2 ^ n * k) hd
    simp only [Nat.mul_add] at he
    simp only [Nat.mul_assoc]
    omega

/-- Binary digits and the carry beyond the last digit are uniquely determined by the
weighted sum, even for words with high zero padding.
Proof sketch. Compare both sums modulo two, cancel their equal low digits, divide by
two, and apply the induction hypothesis to the shifted digit functions. -/
private lemma mult_digits_unique (n k : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ j < n, f j < 2) (hg : ∀ j < n, g j < 2)
    (he : (∑ j ∈ Finset.range n, 2 ^ j * f j) + 2 ^ n * k =
      ∑ j ∈ Finset.range n, 2 ^ j * g j) :
    k = 0 ∧ ∀ j < n, f j = g j := by
  induction n generalizing f g with
  | zero => simpa using he
  | succ n ih =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at he
    simp only [pow_zero, one_mul, pow_succ] at he
    have shift (h : ℕ → ℕ) :
        (∑ j ∈ Finset.range n, 2 ^ j * 2 * h (j + 1)) =
        2 * ∑ j ∈ Finset.range n, 2 ^ j * h (j + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [shift f, shift g] at he
    have hpow : 2 ^ n * 2 * k = 2 * (2 ^ n * k) := by ring
    rw [hpow] at he
    have h₀ : f 0 = g 0 := by have := hf 0 (by omega); have := hg 0 (by omega); omega
    have htail : (∑ j ∈ Finset.range n, 2 ^ j * f (j + 1)) + 2 ^ n * k =
        ∑ j ∈ Finset.range n, 2 ^ j * g (j + 1) := by omega
    obtain ⟨hk, hs⟩ := ih (fun j => f (j + 1)) (fun j => g (j + 1))
      (fun j hj => hf (j + 1) (by omega)) (fun j hj => hg (j + 1) (by omega)) htail
    refine ⟨hk, ?_⟩
    intro j hj
    cases j with
    | zero => exact h₀
    | succ j => exact hs j (by omega)

/-- The finite column checks and final zero carry are exactly the product equation.
The result is zero-padded; its length need only be at most the sum of operand lengths.
Proof sketch. Apply digit uniqueness to the carry invariant and the product expansion.
In the other direction substitute the checked digits and zero carry in that invariant. -/
private lemma mult_columns_correct (a b c : List Bool)
    (hlen : c.length ≤ a.length + b.length) :
    bitsVal c = bitsVal a * bitsVal b ↔
      multCarry a b (a.length + b.length) = 0 ∧
      ∀ j < a.length + b.length,
        (c.getD j false).toNat = (multCarry a b j + multColumn a b j) % 2 := by
  have hv := mult_columns_value a b (a.length + b.length) le_rfl
  have hi := mult_carry_invariant a b (a.length + b.length)
  have hc := mult_bits_prefix c (a.length + b.length)
  rw [List.take_of_length_le hlen] at hc
  constructor
  · intro he
    have heq : (∑ j ∈ Finset.range (a.length + b.length),
        2 ^ j * ((multCarry a b j + multColumn a b j) % 2)) +
        2 ^ (a.length + b.length) * multCarry a b (a.length + b.length) =
        ∑ j ∈ Finset.range (a.length + b.length), 2 ^ j * (c.getD j false).toNat := by
      rw [← hi, hv, hc, he]
    obtain ⟨hzero, hd⟩ := mult_digits_unique _ _ _ _
      (fun j _ => Nat.mod_lt _ (by omega))
      (fun j _ => by cases c.getD j false <;> decide) heq
    exact ⟨hzero, fun j hj => (hd j hj).symm⟩
  · rintro ⟨hzero, hd⟩
    have hs : (∑ j ∈ Finset.range (a.length + b.length),
        2 ^ j * ((multCarry a b j + multColumn a b j) % 2)) = bitsVal c := by
      rw [← hc]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hd j (Finset.mem_range.mp hj)]
    rw [hv, hzero, Nat.mul_zero, Nat.add_zero, hs] at hi
    exact hi.symm

/-- A canonical product needs no more bits than the two operands combined, including zero. -/
private lemma mult_product_length (a b : ℕ) :
    (Nat.bits (a * b)).length ≤ (Nat.bits a).length + (Nat.bits b).length := by
  apply length_bits_le
  rw [pow_add]
  have ha : a < 2 ^ (Nat.bits a).length := by simpa [Nat.size_eq_bits_len] using Nat.lt_size_self a
  have hb : b < 2 ^ (Nat.bits b).length := by simpa [Nat.size_eq_bits_len] using Nat.lt_size_self b
  exact lt_of_le_of_lt (Nat.mul_le_mul_right b ha.le)
    (Nat.mul_lt_mul_of_pos_left hb (Nat.pow_pos (by omega)))

/-- The inner double loop has one possible nonzero summand, at the complementary index.
Proof sketch. If that index is in range, the single-term finite sum rule applies. Otherwise
every equality test fails and the zero-padded lookup is zero as well. -/
private lemma mult_column_row (t : Bool) (b : List Bool) (j p : ℕ) :
    (∑ q ∈ Finset.range b.length,
      if p + q = j then t.toNat * (b.getD q false).toNat else 0) =
    if p ≤ j then t.toNat * (b.getD (j - p) false).toNat else 0 := by
  by_cases hp : p ≤ j
  · rw [if_pos hp]
    by_cases hq : j - p < b.length
    · rw [Finset.sum_eq_single (j - p)]
      · simp [show p + (j-p) = j by omega]
      · intro q hq hne
        rw [if_neg (by omega)]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr hq))
    · have hzero : b.getD (j-p) false = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : b.length ≤ j-p)]
      rw [hzero]
      simp only [Bool.toNat_false, Nat.mul_zero]
      apply Finset.sum_eq_zero
      intro q hmem
      rw [if_neg (by have := Finset.mem_range.mp hmem; omega)]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg (by omega)]

/-- The literal double loop computes the column used in the carry invariant. -/
private lemma mult_column_double (a b : List Bool) (j : ℕ) :
    (∑ p ∈ Finset.range a.length, ∑ q ∈ Finset.range b.length,
      if p + q = j then (a.getD p false).toNat * (b.getD q false).toNat else 0) =
      multColumn a b j := by
  unfold multColumn
  apply Finset.sum_congr rfl
  intro p hp
  exact mult_column_row (a.getD p false) b j p

/-- Contributions remaining in one inner loop, with an arbitrary starting diagonal index. -/
private def multRow (t : Bool) (b : List Bool) (j k : ℕ) : ℕ :=
  ∑ q ∈ Finset.range b.length,
    if k + q = j then t.toNat * (b.getD q false).toNat else 0

/-- Removing the next second-operand bit exposes one tested contribution. -/
private lemma multRow_cons (t u : Bool) (b : List Bool) (j k : ℕ) :
    multRow t (u :: b) j k =
      (if k = j then t.toNat * u.toNat else 0) + multRow t b j (k + 1) := by
  simp only [multRow, List.length_cons, Finset.sum_range_succ']
  simp [Nat.add_left_comm, Nat.add_comm]

/-- Only one second-operand index can contribute to a fixed row and column. -/
private lemma multRow_le_one (t : Bool) (b : List Bool) (j k : ℕ) : multRow t b j k ≤ 1 := by
  rw [multRow, mult_column_row]
  split_ifs
  · cases t <;> cases b.getD (j-k) false <;> decide
  · omega

/-- Remaining first-operand rows in a column, with an arbitrary starting first index. -/
private def multRows (a b : List Bool) (j p : ℕ) : ℕ :=
  ∑ q ∈ Finset.range a.length, multRow (a.getD q false) b j (p + q)

/-- The first row separates from the remaining outer loop. -/
private lemma multRows_cons (t : Bool) (a b : List Bool) (j p : ℕ) :
    multRows (t :: a) b j p = multRow t b j p + multRows a b j (p + 1) := by
  simp only [multRows, List.length_cons, Finset.sum_range_succ']
  simp [Nat.add_left_comm, Nat.add_comm]

/-- A remaining outer loop contributes at most one per remaining first-operand bit. -/
private lemma multRows_bound (a b : List Bool) (j p : ℕ) : multRows a b j p ≤ a.length := by
  calc
    _ ≤ ∑ _q ∈ Finset.range a.length, 1 := Finset.sum_le_sum (fun q _ => multRow_le_one _ _ _ _)
    _ = a.length := by simp

/-- Starting both loops at their first indices produces the convolution column. -/
private lemma multRows_column (a b : List Bool) (j : ℕ) : multRows a b j 0 = multColumn a b j := by
  simpa only [multRows, multRow, Nat.zero_add] using mult_column_double a b j

/-- Canonicality is decided from emptiness and the last bit, without storing the value. -/
private lemma mult_canonical_last (w : List Bool) :
    Canon w ↔ w.length = 0 ∨ w.getD (w.length - 1) false = true := by
  by_cases hw : w = []
  · subst w; simp [Canon]
  · have hn : 0 < w.length := List.length_pos_iff.mpr hw
    simp only [Canon, Nat.ne_of_gt hn, false_or]
    have hget : w.getD (w.length - 1) false = w.getLast hw := by
      simp [List.getLast_eq_getElem, List.getD_eq_getElem?_getD, show w.length - 1 < w.length by omega]
    rw [hget]
    exact ⟨fun h => h hw, fun h _ => h⟩

/-- Pair injectivity and canonical binary uniqueness identify the existential language
with the arithmetic predicate on the three parsed words. -/
private lemma mult_membership (a b c : List Bool) :
    pairEncode a (pairEncode b c) ∈ multLang ↔
      Canon a ∧ Canon b ∧ Canon c ∧ bitsVal c = bitsVal a * bitsVal b := by
  constructor
  · rintro ⟨u, v, he⟩
    obtain ⟨ha, hbc⟩ := Prod.mk.inj (pairEncode_injective he)
    obtain ⟨hb, hc⟩ := Prod.mk.inj (pairEncode_injective hbc)
    subst a; subst b; subst c
    exact ⟨canon_bits u, canon_bits v, canon_bits (u * v), by
      change bitsVal (Nat.bits (u * v)) = bitsVal (Nat.bits u) * bitsVal (Nat.bits v)
      simp only [bitsVal_bits]⟩
  · rintro ⟨ha, hb, hc, he⟩
    refine ⟨bitsVal a, bitsVal b, ?_⟩
    rw [← he, ← canon_eq_bits a ha, ← canon_eq_bits b hb, ← canon_eq_bits c hc]

/-- The complete arithmetic acceptance condition, including canonicality and excessive
result-length rejection, is equivalent to membership in `MULT`.
Proof sketch. Canonicality fixes each field to the binary representation of its value.
The product-length bound supplies the legal column count; `mult_columns_correct` supplies
exactly the parity comparisons and final carry test. -/
private lemma mult_acceptance (a b c : List Bool) :
    pairEncode a (pairEncode b c) ∈ multLang ↔
      Canon a ∧ Canon b ∧ Canon c ∧ c.length ≤ a.length + b.length ∧
      multCarry a b (a.length + b.length) = 0 ∧
      ∀ j < a.length + b.length,
        (c.getD j false).toNat = (multCarry a b j + multColumn a b j) % 2 := by
  rw [mult_membership]
  constructor
  · rintro ⟨ha, hb, hc, he⟩
    have hlen : c.length ≤ a.length + b.length := by
      rw [canon_eq_bits c hc, canon_eq_bits a ha, canon_eq_bits b hb, he]
      exact mult_product_length _ _
    exact ⟨ha, hb, hc, hlen, (mult_columns_correct a b c hlen).mp he⟩
  · rintro ⟨ha, hb, hc, hlen, hcheck⟩
    exact ⟨ha, hb, hc, (mult_columns_correct a b c hlen).mpr hcheck⟩

open LogProg Turing Classical

/-- Finite control for the multiplication verifier. The two shape scans have stride one.
Registers 0–12 hold: the first pointer, host length, second and third starts, first and
second ends, column count, current column, first index, second pointer, index sum,
carry/accumulator and result pointer. -/
private inductive MultState
  | lengthTest | lengthInc
  | pairTest (inner : Bool) | pairFirst (inner : Bool)
  | pairSecond (inner bit : Bool) | pairRead (inner bit : Bool)
  | pairAdvance (inner : Bool) (choice : Fin 4)
  | copy (stage : Fin 11) (bump : Bool)
  | endDown (inner second : Bool)
  | countHalf | countDown (second : Bool)
  | canonTest (field : Fin 3) | canonClear (field : Fin 3)
  | canonDown (field : Fin 3) (second : Bool) | canonRead (field : Fin 3)
  | column | clearA | clearP | outer | clearB | clearDiagonal | inner
  | diagonal | firstBit | secondBit | add
  | nextB (second : Bool) | nextDiagonal
  | nextA (second : Bool) | nextP
  | resultTest | resultRead | parity (bit : Bool)
  | carryHalf | nextColumn | nextResultTest | nextResult
  | finalPosition | finalCarry | answer (bit : Bool)
  deriving DecidableEq, Fintype

/-- Continuations of the two received shape scans. -/
private def multPairNext (inner : Bool) (choice : Fin 4) : MultState :=
  ![.pairSecond inner false, .pairSecond inner true, .pairTest inner,
    .copy (if inner then 1 else 0) false] choice

/-- Copy destinations, sources, and successful continuations. Every copy is the received
bounded counting fragment; the caller clears a reused destination before entering. -/
private def multCopy : Fin 11 → Fin 13 × Fin 13 × MultState :=
  ![(2, 0, .pairTest true), (3, 0, .copy 2 false),
    (4, 2, .endDown false false), (5, 3, .endDown true false),
    (6, 3, .countHalf),
    (0, 4, .canonDown 0 false), (0, 5, .canonDown 1 false),
    (0, 1, .canonDown 2 false), (12, 3, .column),
    (9, 2, .clearDiagonal), (10, 8, .inner)]

/-- The complete finite table for [AB09, Example 4.7]. All input reads are whole-mode
calls to the two proved input-access languages. No field value is stored. Two nested
loops enumerate operand positions in each column. The result pointer stops at its end,
so missing bits compare with zero; the final position test rejects an overlong result. -/
private def multARM : ARM 13 2 MultState
  | .lengthTest => .call 1 .whole [1] .lengthInc (.pairTest false)
  | .lengthInc => .inc 1 .lengthTest
  | .pairTest inner => .jeq 0 1 (.answer false) (.pairFirst inner)
  | .pairFirst inner => .call 0 .whole [0] (.pairAdvance inner 1) (.pairAdvance inner 0)
  | .pairSecond inner bit => .jeq 0 1 (.answer false) (.pairRead inner bit)
  | .pairRead inner bit => .call 0 .whole [0]
      (if bit then .pairAdvance inner 2 else .pairAdvance inner 3)
      (if bit then .answer false else .pairAdvance inner 2)
  | .pairAdvance inner choice => .inc 0 (multPairNext inner choice)
  | .copy stage false => .jeq (multCopy stage).1 (multCopy stage).2.1
      (multCopy stage).2.2 (.copy stage true)
  | .copy stage true => .inc (multCopy stage).1 (.copy stage false)
  | .endDown inner false => .dec (if inner then 5 else 4) (.endDown inner true)
  | .endDown inner true => .dec (if inner then 5 else 4) (.copy (if inner then 4 else 3) false)
  | .countHalf => .half 6 (.countDown false)
  | .countDown false => .dec 6 (.countDown true)
  | .countDown true => .dec 6 (.canonTest 0)
  | .canonTest f =>
      if f = 0 then .jz 4 (.canonTest 1) (.canonClear 0)
      else if f = 1 then .jeq 5 2 (.canonTest 2) (.canonClear 1)
      else .jeq 3 1 (.copy 8 false) (.canonClear 2)
  | .canonClear f => .clr 0 (.copy (if f = 0 then 5 else if f = 1 then 6 else 7) false)
  | .canonDown f second => .dec 0
      (if f = 2 ∨ second = true then .canonRead f else .canonDown f true)
  | .canonRead f => .call 0 .whole [0]
      (if f = 0 then .canonTest 1 else if f = 1 then .canonTest 2 else .copy 8 false)
      (.answer false)
  | .column => .jeq 7 6 .finalPosition .clearA
  | .clearA => .clr 0 .clearP
  | .clearP => .clr 8 .outer
  | .outer => .jeq 0 4 .resultTest .clearB
  | .clearB => .clr 9 (.copy 9 false)
  | .clearDiagonal => .clr 10 (.copy 10 false)
  | .inner => .jeq 9 5 (.nextA false) .diagonal
  | .diagonal => .jeq 10 7 .firstBit (.nextB false)
  | .firstBit => .call 0 .whole [0] .secondBit (.nextB false)
  | .secondBit => .call 0 .whole [9] .add (.nextB false)
  | .add => .inc 11 (.nextB false)
  | .nextB false => .inc 9 (.nextB true)
  | .nextB true => .inc 9 .nextDiagonal
  | .nextDiagonal => .inc 10 .inner
  | .nextA false => .inc 0 (.nextA true)
  | .nextA true => .inc 0 .nextP
  | .nextP => .inc 8 .outer
  | .resultTest => .jeq 12 1 (.parity false) .resultRead
  | .resultRead => .call 0 .whole [12] (.parity true) (.parity false)
  | .parity bit => .jodd 11 (if bit then .carryHalf else .answer false)
      (if bit then .answer false else .carryHalf)
  | .carryHalf => .half 11 .nextColumn
  | .nextColumn => .inc 7 .nextResultTest
  | .nextResultTest => .jeq 12 1 .column .nextResult
  | .nextResult => .inc 12 .column
  | .finalPosition => .jeq 12 1 .finalCarry (.answer false)
  | .finalCarry => .jz 11 (.answer true) (.answer false)
  | .answer bit => .ret bit

/-- The three physical addresses in the nested-pair layout, from the frozen common
pair lookup law. The result-field equation includes its zero padding. -/
private lemma mult_addresses (a b c : List Bool) :
    (∀ i < a.length, (pairEncode a (pairEncode b c)).getD (2 * i) false = a.getD i false) ∧
    (∀ i < b.length, (pairEncode a (pairEncode b c)).getD (2 * a.length + 2 + 2 * i) false =
      b.getD i false) ∧
    (∀ i, (pairEncode a (pairEncode b c)).getD (2 * a.length + 2 + 2 * b.length + 2 + i) false =
      c.getD i false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  · intro i hi
    rw [pairEncode_getD_snd, pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  · intro i
    rw [show 2 * a.length + 2 + 2 * b.length + 2 + i = 2 * a.length + 2 + (2 * b.length + 2 + i)
      by omega, pairEncode_getD_snd, pairEncode_getD_snd]

/-- Conditions not yet checked at the start of column `j`. -/
private def MultRemaining (a b c : List Bool) (j : ℕ) : Prop :=
  c.length ≤ a.length + b.length ∧ multCarry a b (a.length + b.length) = 0 ∧
    ∀ i, j ≤ i → i < a.length + b.length →
      (c.getD i false).toNat = (multCarry a b i + multColumn a b i) % 2

/-- The residual acceptance condition separates into the next bit and the later columns. -/
private lemma mult_remaining_step (a b c : List Bool) (j : ℕ) (hj : j < a.length + b.length) :
    MultRemaining a b c j ↔
      (c.getD j false).toNat = (multCarry a b j + multColumn a b j) % 2 ∧
      MultRemaining a b c (j + 1) := by
  constructor
  · rintro ⟨hlen, hzero, hbits⟩
    exact ⟨hbits j le_rfl hj, hlen, hzero, fun i hi hin => hbits i (by omega) hin⟩
  · rintro ⟨hbit, hlen, hzero, hbits⟩
    refine ⟨hlen, hzero, ?_⟩
    intro i hi hin
    by_cases he : i = j
    · simpa only [he] using hbit
    · exact hbits i (by omega) hin

/-- Truthful access-bank oracle used throughout the run proof. -/
private noncomputable def multOracle : Fin 2 → List Bool → Bool :=
  fun k => MultiTapeTM.indicator ((![inputBitLang, inputLenLang] k : Language Bool) : Set (List Bool))

/-- Both genuine-query equations follow from the frozen index-language indicator law. -/
private lemma mult_queries (x : List Bool) (i : ℕ) :
    multOracle 0 (pairEncode x (Nat.bits i)) = x.getD i false ∧
    multOracle 1 (pairEncode x (Nat.bits i)) = decide (i < x.length) := by
  exact ⟨show MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _ from
      indicator_inputBitLang x i,
    show MultiTapeTM.indicator (inputLenLang : Set (List Bool)) _ = _ from
      indicator_inputLenLang x i⟩

/-- All table instructions meet their syntactic side conditions for every input and
register assignment: comparisons use distinct registers and calls use one register. -/
private lemma mult_preconditions (x : List Bool) (s : MultState) (v : Fin 13 → ℕ)
    (o : Option Bool) : PreS multARM x (some s, v, o) := by
  cases s <;> simp only [PreS, multARM] <;> try decide
  case copy stage bump =>
    cases bump
    · exact (by decide : ∀ k, (multCopy k).1 ≠ (multCopy k).2.1) stage
    · trivial
  case canonTest field => split_ifs <;> simp
  case endDown inner second => cases second <;> trivial
  case countDown second => cases second <;> trivial
  case nextB second => cases second <;> trivial
  case nextA second => cases second <;> trivial

/-- The syntactic and numerical guard shared by all bounded multiplication paths. -/
private abbrev MultGood (x : List Bool) (a : AConf 13 MultState) :=
  PreS multARM x a ∧ ∀ r, a.2.1 r ≤ 4 * (x.length + 1)

/-- The received bounded path relation at the required linear register bound. -/
private abbrev MultReach (x : List Bool) :=
  AReach multARM multOracle x (MultGood x)

/-- The received bounded halting relation at the same bound. -/
private abbrev MultHalt (x : List Bool) :=
  AHalt multARM multOracle x (MultGood x)

/-- Every copy stage invokes the public bounded copy fragment. -/
private lemma mult_copy (x : List Bool) (k : Fin 11) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (ordered : v (multCopy k).1 ≤ v (multCopy k).2.1) :
    MultReach x (some (.copy k false), v, none)
      (some (multCopy k).2.2, Function.update v (multCopy k).1 (v (multCopy k).2.1), none) :=
  registerCopy_loop multARM multOracle x (multCopy k).1 (multCopy k).2.1
    ((by decide : ∀ k, (multCopy k).1 ≠ (multCopy k).2.1) k)
    (.copy k false) (.copy k true) (multCopy k).2.2 rfl rfl _ v bound ordered

/-- Both shape scans instantiate the same public aligned-pair validator. -/
private lemma mult_scan (x w : List Bool) (inner : Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) (endpos : v 1 = v 0 + w.length)
    (reads : ∀ j < w.length, x.getD (v 0 + j) false = w.getD j false) :
    match pairDecode w with
    | none => ∃ t ≤ w.length, MultReach x (some (.pairTest inner), v, none)
        (some (.answer false), Function.update v 0 (v 0 + t), none)
    | some (a, _) => MultReach x (some (.pairTest inner), v, none)
        (some (.copy (if inner then 1 else 0) false),
          Function.update v 0 (v 0 + (2 * a.length + 2)), none) := by
  let advance : Fin 4 → ℕ → MultState := fun k t =>
    if t = 0 then .pairAdvance inner k else multPairNext inner k
  have paths := alignedPair_loop multARM multOracle x 0 1 0
    (.pairTest inner) (.pairFirst inner) (.pairSecond inner) (.pairRead inner)
    (.answer false) (.copy (if inner then 1 else 0) false) advance 1
    (4 * (x.length + 1)) (by omega) (by decide) rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun k i hi => by
      have hi0 : i = 0 := by omega
      subst i
      rfl)
    (by simp [advance, multPairNext]) w v bound (by simpa using endpos)
    (fun j hj => by simpa only [one_mul, (mult_queries x _).1] using reads j hj)
  simpa only [one_mul] using paths

/-- A tested pair contributes its product exactly when its two indices name the current
column. This path stops immediately after the possible increment, before the next loop step. -/
private lemma mult_contribution (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultReach x (some .diagonal, v, none)
      (some (.nextB false), Function.update v 11
        (v 11 + if v 10 = v 7 then
          (x.getD (v 0) false).toNat * (x.getD (v 9) false).toNat else 0), none) := by
  have good (s : MultState) : PreS multARM x (some s, v, none) ∧
      ∀ r, v r ≤ 4 * (x.length + 1) := ⟨mult_preconditions x s v none, bound⟩
  apply AReach.step (good .diagonal)
  simp only [astep_jeq (show multARM .diagonal = _ from rfl)]
  by_cases eq : v 10 = v 7
  · rw [if_pos eq, if_pos eq]
    apply AReach.step (good .firstBit)
    simp only [astep_call (show multARM .firstBit = _ from rfl), vword_whole₁, (mult_queries x _).1]
    cases first : x.getD (v 0) false with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false,
        Nat.zero_mul, Nat.add_zero, Function.update_eq_self]
      exact AReach.refl _
    | true =>
      simp only [↓reduceIte, Bool.toNat_true, Nat.one_mul]
      apply AReach.step (good .secondBit)
      simp only [astep_call (show multARM .secondBit = _ from rfl), vword_whole₁,
        (mult_queries x _).1]
      cases second : x.getD (v 9) false with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false,
          Nat.add_zero, Function.update_eq_self]
        exact AReach.refl _
      | true =>
        simp only [↓reduceIte, Bool.toNat_true]
        exact AReach.single (good .add)
  · simp only [if_neg eq, Nat.add_zero, Function.update_eq_self]
    exact AReach.refl _

/-- The inner operand loop terminates and adds exactly its row contribution, preserving
all other registers. The hypotheses bound the final accumulator and index; monotonicity
then bounds every intermediate increment.
Proof sketch. Induct on the remaining second-operand word. The diagonal and two oracle
reads give one contribution, then two pointer increments and one index increment expose
the tail. The empty word exits by the end-address comparison. -/
private lemma mult_inner_loop (x : List Bool) (bit : Bool) (w : List Bool)
    (v : Fin 13 → ℕ) (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (endpos : v 5 = v 9 + 2 * w.length)
    (first : x.getD (v 0) false = bit)
    (reads : ∀ q < w.length, x.getD (v 9 + 2 * q) false = w.getD q false)
    (indexBound : v 10 + w.length ≤ 4 * (x.length + 1))
    (sumBound : v 11 + multRow bit w (v 7) (v 10) ≤ 4 * (x.length + 1)) :
    MultReach x (some .inner, v, none)
      (some (.nextA false),
        Function.update (Function.update (Function.update v 9 (v 9 + 2 * w.length))
          10 (v 10 + w.length)) 11 (v 11 + multRow bit w (v 7) (v 10)), none) := by
  induction w generalizing v with
  | nil =>
    have ends : v 9 = v 5 := by simpa using endpos.symm
    simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero, multRow,
      Finset.range_zero, Finset.sum_empty, Function.update_eq_self,
      astep_jeq (show multARM .inner = _ from rfl),
      if_pos ends] using (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some .inner, v, none)) ⟨mult_preconditions x .inner v none, bound⟩)
  | cons u w ih =>
    let delta := if v 10 = v 7 then bit.toNat * u.toNat else 0
    let va := Function.update v 11 (v 11 + delta)
    let v₁ := Function.update va 9 (v 9 + 1)
    let v₂ := Function.update va 9 (v 9 + 2)
    let vn := Function.update v₂ 10 (v 10 + 1)
    have cap : v 11 + delta + multRow bit w (v 7) (v 10 + 1) ≤ 4 * (x.length + 1) := by
      rw [multRow_cons] at sumBound
      dsimp [delta]
      omega
    have ba : ∀ r, va r ≤ 4 * (x.length + 1) := register_update_le v 11 _ _ bound (by omega)
    have b₁ : ∀ r, v₁ r ≤ 4 * (x.length + 1) := by
      apply register_update_le va 9 _ _ ba
      have := bound 5
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at endpos
      omega
    have b₂ : ∀ r, v₂ r ≤ 4 * (x.length + 1) := by
      apply register_update_le va 9 _ _ ba
      have := bound 5
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at endpos
      omega
    have bn : ∀ r, vn r ≤ 4 * (x.length + 1) := by
      apply register_update_le v₂ 10 _ _ b₂
      simp only [List.length_cons] at indexBound
      omega
    have headRead : x.getD (v 9) false = u := by simpa using reads 0 (by simp)
    have pairStep : MultReach x (some .diagonal, v, none) (some (.nextB false), va, none) := by
      simpa only [first, headRead] using mult_contribution x v bound
    have adv₁ : MultReach x (some (.nextB false), va, none) (some (.nextB true), v₁, none) :=
      AReach.single ⟨mult_preconditions x _ va none, ba⟩
    have adv₂ : MultReach x (some (.nextB true), v₁, none) (some .nextDiagonal, v₂, none) := by
      simpa [astep_inc (show multARM (.nextB true) = _ from rfl), v₁, v₂, Function.update_idem,
        Nat.add_assoc] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some (.nextB true), v₁, none)) ⟨mult_preconditions x _ v₁ none, b₁⟩)
    have adv₃ : MultReach x (some .nextDiagonal, v₂, none) (some .inner, vn, none) :=
      AReach.single ⟨mult_preconditions x _ v₂ none, b₂⟩
    have hnend : vn 5 = vn 9 + 2 * w.length := by
      simp [vn, v₂, va]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at endpos
      omega
    have hnfirst : x.getD (vn 0) false = bit := by simpa [vn, v₂, va] using first
    have hnreads : ∀ q < w.length, x.getD (vn 9 + 2 * q) false = w.getD q false := by
      intro q hq
      have hq' := reads (q + 1) (by simp; omega)
      simpa [vn, v₂, va, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hq'
    have hnindex : vn 10 + w.length ≤ 4 * (x.length + 1) := by
      simpa [vn, Nat.add_assoc, Nat.add_comm] using indexBound
    have hnsum : vn 11 + multRow bit w (vn 7) (vn 10) ≤ 4 * (x.length + 1) := by
      simpa [vn, v₂, va] using cap
    have rest := ih vn bn hnend hnfirst hnreads hnindex hnsum
    have endpoints : Function.update (Function.update (Function.update vn 9
        (vn 9 + 2 * w.length)) 10 (vn 10 + w.length))
        11 (vn 11 + multRow bit w (vn 7) (vn 10)) =
        Function.update (Function.update (Function.update v 9 (v 9 + 2 * (u :: w).length))
          10 (v 10 + (u :: w).length)) 11 (v 11 + multRow bit (u :: w) (v 7) (v 10)) := by
      simp [funext_iff, Fin.forall_fin_succ, Function.update_apply, vn, v₂, va,
        multRow_cons, delta, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [endpoints] at rest
    apply AReach.step ⟨mult_preconditions x .inner v none, bound⟩
    have hne : v 9 ≠ v 5 := by simp only [List.length_cons] at endpos; omega
    simpa only [astep_jeq (show multARM .inner = _ from rfl), if_neg hne] using
      pairStep.trans (adv₁.trans (adv₂.trans (adv₃.trans rest)))

/-- Clear and restore the second pointer and diagonal index before an inner loop.
Both restorations invoke the single shared counting-copy proof. -/
private lemma mult_row_start (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultReach x (some .clearB, v, none)
      (some .inner, Function.update (Function.update v 9 (v 2)) 10 (v 8), none) := by
  let va := Function.update v 9 0
  let vb := Function.update v 9 (v 2)
  let vc := Function.update vb 10 0
  have ba : ∀ r, va r ≤ 4 * (x.length + 1) := register_update_le v 9 _ _ bound (Nat.zero_le _)
  have bb : ∀ r, vb r ≤ 4 * (x.length + 1) := register_update_le v 9 _ _ bound (bound 2)
  have bc : ∀ r, vc r ≤ 4 * (x.length + 1) := register_update_le vb 10 _ _ bb (Nat.zero_le _)
  have cp₁ : MultReach x (some (.copy 9 false), va, none) (some .clearDiagonal, vb, none) := by
    simpa [multCopy, va, vb] using mult_copy x 9 va ba (by simp [multCopy, va])
  have cp₂ : MultReach x (some (.copy 10 false), vc, none)
      (some .inner, Function.update vb 10 (v 8), none) := by
    simpa [multCopy, vc, vb] using mult_copy x 10 vc bc (by simp [multCopy, vc])
  apply AReach.step ⟨mult_preconditions x .clearB v none, bound⟩
  change MultReach x (some (.copy 9 false), va, none) _
  apply cp₁.trans
  apply AReach.step ⟨mult_preconditions x .clearDiagonal vb none, bb⟩
  exact cp₂

/-- The complete outer operand loop computes all remaining rows of one column.
Proof sketch. Reset the inner counters through the public copy fragment, apply the proved
inner loop to the next first-operand bit, and advance that bit's pointer and index. Induct
on the remaining first-operand word. The total remaining row sum bounds the accumulator
through each nested loop; the sum of remaining lengths bounds the index additions. -/
private lemma mult_outer_loop (x a b : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (enda : v 4 = v 0 + 2 * a.length) (endb : v 5 = v 2 + 2 * b.length)
    (readsa : ∀ p < a.length, x.getD (v 0 + 2 * p) false = a.getD p false)
    (readsb : ∀ q < b.length, x.getD (v 2 + 2 * q) false = b.getD q false)
    (indexBound : v 8 + a.length + b.length ≤ 4 * (x.length + 1))
    (sumBound : v 11 + multRows a b (v 7) (v 8) ≤ 4 * (x.length + 1)) :
    ∃ final : Fin 13 → ℕ,
      (∀ r, final r ≤ 4 * (x.length + 1)) ∧
      final 0 = v 0 + 2 * a.length ∧ final 8 = v 8 + a.length ∧
      final 11 = v 11 + multRows a b (v 7) (v 8) ∧
      (∀ r, r ≠ 0 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → final r = v r) ∧
      MultReach x (some .outer, v, none) (some .resultTest, final, none) := by
  induction a generalizing v with
  | nil =>
    refine ⟨v, bound, by simp, by simp, by simp [multRows], ?_, ?_⟩
    · intros; rfl
    · have he : v 0 = v 4 := by simpa using enda.symm
      simpa only [astep_jeq (show multARM .outer = _ from rfl), if_pos he] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some .outer, v, none)) ⟨mult_preconditions x .outer v none, bound⟩)
  | cons t a ih =>
    let vs := Function.update (Function.update v 9 (v 2)) 10 (v 8)
    let ve := Function.update (Function.update (Function.update v 9 (v 2 + 2 * b.length))
      10 (v 8 + b.length)) 11 (v 11 + multRow t b (v 7) (v 8))
    let v₁ := Function.update ve 0 (v 0 + 1)
    let v₂ := Function.update ve 0 (v 0 + 2)
    let vn := Function.update v₂ 8 (v 8 + 1)
    have cap : v 11 + multRow t b (v 7) (v 8) + multRows a b (v 7) (v 8 + 1) ≤
        4 * (x.length + 1) := by rw [multRows_cons] at sumBound; omega
    have bs : ∀ r, vs r ≤ 4 * (x.length + 1) :=
      register_update_le _ 10 _ _ (register_update_le v 9 _ _ bound (bound 2)) (bound 8)
    have be : ∀ r, ve r ≤ 4 * (x.length + 1) := by
      apply register_update_le _ 11 _ _
      · apply register_update_le _ 10 _ _
        · apply register_update_le v 9 _ _ bound
          rw [← endb]; exact bound 5
        · simp only [List.length_cons] at indexBound; omega
      · omega
    have b₁ : ∀ r, v₁ r ≤ 4 * (x.length + 1) := by
      apply register_update_le ve 0 _ _ be
      have := bound 4
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at enda
      omega
    have b₂ : ∀ r, v₂ r ≤ 4 * (x.length + 1) := by
      apply register_update_le ve 0 _ _ be
      have := bound 4
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at enda
      omega
    have bn : ∀ r, vn r ≤ 4 * (x.length + 1) := by
      apply register_update_le v₂ 8 _ _ b₂
      simp only [List.length_cons] at indexBound; omega
    have starts := mult_row_start x v bound
    have inner := mult_inner_loop x t b vs bs
      (by simpa [vs] using endb)
      (by simpa [vs] using readsa 0 (by simp))
      (by simpa [vs] using readsb)
      (by simp [vs]; simp only [List.length_cons] at indexBound; omega)
      (by simp [vs]; omega)
    have innerEnd : Function.update (Function.update (Function.update vs 9
        (vs 9 + 2 * b.length)) 10 (vs 10 + b.length))
        11 (vs 11 + multRow t b (vs 7) (vs 10)) = ve := by
      simp [funext_iff, Fin.forall_fin_succ, Function.update_apply, vs, ve]
    rw [innerEnd] at inner
    have adv₁ : MultReach x (some (.nextA false), ve, none) (some (.nextA true), v₁, none) :=
      AReach.single ⟨mult_preconditions x _ ve none, be⟩
    have adv₂ : MultReach x (some (.nextA true), v₁, none) (some .nextP, v₂, none) := by
      simpa [astep_inc (show multARM (.nextA true) = _ from rfl), v₁, v₂, Function.update_idem,
        Nat.add_assoc] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some (.nextA true), v₁, none)) ⟨mult_preconditions x _ v₁ none, b₁⟩)
    have adv₃ : MultReach x (some .nextP, v₂, none) (some .outer, vn, none) :=
      AReach.single ⟨mult_preconditions x _ v₂ none, b₂⟩
    have hna : vn 4 = vn 0 + 2 * a.length := by
      simp [vn, v₂, ve]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at enda
      omega
    have hnb : vn 5 = vn 2 + 2 * b.length := by simpa [vn, v₂, ve] using endb
    have hnread : ∀ p < a.length, x.getD (vn 0 + 2 * p) false = a.getD p false := by
      intro p hp
      have h := readsa (p + 1) (by simp; omega)
      simpa [vn, v₂, ve, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
    have hnreadb : ∀ q < b.length, x.getD (vn 2 + 2 * q) false = b.getD q false := by
      simpa [vn, v₂, ve] using readsb
    have hni : vn 8 + a.length + b.length ≤ 4 * (x.length + 1) := by
      simpa [vn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using indexBound
    have hnc : vn 11 + multRows a b (vn 7) (vn 8) ≤ 4 * (x.length + 1) := by
      simpa [vn, v₂, ve] using cap
    obtain ⟨last, bl, la, lp, lc, frame, rest⟩ := ih vn bn hna hnb hnread hnreadb hni hnc
    refine ⟨last, bl, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [vn, v₂, ve, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using la
    · simpa [vn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using lp
    · simpa [vn, v₂, ve, multRows_cons, Nat.add_assoc] using lc
    · intro r r0 r8 r9 r10 r11
      rw [frame r r0 r8 r9 r10 r11]
      simp [vn, v₂, ve, Function.update_of_ne, r0, r8, r9, r10, r11]
    · apply AReach.step ⟨mult_preconditions x .outer v none, bound⟩
      have ne : v 0 ≠ v 4 := by simp only [List.length_cons] at enda; omega
      simpa only [astep_jeq (show multARM .outer = _ from rfl), if_neg ne] using
        starts.trans (inner.trans (adv₁.trans (adv₂.trans (adv₃.trans rest))))

/-- Returning from a Boolean exit uses the received one-step halting rule. -/
private lemma mult_return (x : List Bool) (bit : Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultHalt x (some (.answer bit), v, none) bit :=
  AHalt.ret rfl ⟨mult_preconditions x (.answer bit) v none, bound⟩

/-- The final two tests accept exactly exhausted result input and zero carry. -/
private lemma mult_finish (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultHalt x (some .finalPosition, v, none) (decide (v 12 = v 1 ∧ v 11 = 0)) := by
  apply AHalt.step ⟨mult_preconditions x .finalPosition v none, bound⟩
  simp only [astep_jeq (show multARM .finalPosition = _ from rfl)]
  by_cases hp : v 12 = v 1
  · rw [if_pos hp]
    apply AHalt.step ⟨mult_preconditions x .finalCarry v none, bound⟩
    simp only [astep_jz (show multARM .finalCarry = _ from rfl)]
    by_cases hc : v 11 = 0 <;> simpa [hp, hc] using mult_return x (decide (v 11 = 0)) v bound
  · simpa [hp] using mult_return x false v bound

/-- A parity test either reaches carry propagation or rejects the supplied result bit. -/
private lemma mult_parity (x : List Bool) (v : Fin 13 → ℕ) (bit : Bool)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    if bit.toNat = v 11 % 2 then
      MultReach x (some (.parity bit), v, none) (some .carryHalf, v, none)
    else MultHalt x (some (.parity bit), v, none) false := by
  have hmod := Nat.mod_lt (v 11) (by omega : 0 < 2)
  cases bit <;> by_cases odd : v 11 % 2 = 1
  all_goals simp only [Bool.toNat_false, Bool.toNat_true]
  · rw [if_neg (by omega)]
    apply AHalt.step ⟨mult_preconditions x _ v none, bound⟩
    simpa [astep_jodd (show multARM (.parity false) = _ from rfl), odd] using
      mult_return x false v bound
  · rw [if_pos (by omega)]
    simpa [astep_jodd (show multARM (.parity false) = _ from rfl), odd] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some (.parity false), v, none)) ⟨mult_preconditions x _ v none, bound⟩)
  · rw [if_pos odd.symm]
    simpa [astep_jodd (show multARM (.parity true) = _ from rfl), odd] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some (.parity true), v, none)) ⟨mult_preconditions x _ v none, bound⟩)
  · rw [if_neg (by omega)]
    apply AHalt.step ⟨mult_preconditions x _ v none, bound⟩
    simpa [astep_jodd (show multARM (.parity true) = _ from rfl), odd] using
      mult_return x false v bound

/-- At the result end the next bit is zero; otherwise the access bank reads it. -/
private lemma mult_result_read (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) (length : v 1 = x.length) :
    MultReach x (some .resultTest, v, none)
      (some (.parity (x.getD (v 12) false)), v, none) := by
  apply AReach.step ⟨mult_preconditions x .resultTest v none, bound⟩
  simp only [astep_jeq (show multARM .resultTest = _ from rfl)]
  by_cases hp : v 12 = v 1
  · have hzero : x.getD (v 12) false = false := by
      simp [hp, length, List.getD_eq_getElem?_getD]
    rw [if_pos hp, hzero]
    exact AReach.refl _
  · rw [if_neg hp]
    cases hb : x.getD (v 12) false <;>
      simpa only [astep_call (show multARM .resultRead = _ from rfl), vword_whole₁,
        (mult_queries x _).1,
        hb, Bool.false_eq_true, ↓reduceIte] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (G := fun a => PreS multARM x a ∧ ∀ r, a.2.1 r ≤ 4 * (x.length + 1))
        (a := (some .resultRead, v, none)) ⟨mult_preconditions x _ v none, bound⟩)

/-- Carry halving and bounded cursor advancement prepare the next column. The result
pointer saturates at the input end rather than requiring equal operand/product lengths. -/
private lemma mult_next_column (x : List Bool) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) (position : v 12 ≤ v 1)
    (columnBound : v 7 + 1 ≤ 4 * (x.length + 1)) :
    MultReach x (some .carryHalf, v, none)
      (some .column, Function.update (Function.update (Function.update v 11 (v 11 / 2))
        7 (v 7 + 1)) 12 (min (v 12 + 1) (v 1)), none) := by
  let vh := Function.update v 11 (v 11 / 2)
  let vi := Function.update vh 7 (v 7 + 1)
  have bh : ∀ r, vh r ≤ 4 * (x.length + 1) :=
    register_update_le v 11 _ _ bound ((Nat.div_le_self _ _).trans (bound 11))
  have bi : ∀ r, vi r ≤ 4 * (x.length + 1) := register_update_le vh 7 _ _ bh columnBound
  apply AReach.step ⟨mult_preconditions x .carryHalf v none, bound⟩
  change MultReach x (some .nextColumn, vh, none) _
  apply AReach.step ⟨mult_preconditions x .nextColumn vh none, bh⟩
  change MultReach x (some .nextResultTest, vi, none) _
  apply AReach.step ⟨mult_preconditions x .nextResultTest vi none, bi⟩
  simp only [astep_jeq (show multARM .nextResultTest = _ from rfl)]
  have vp : vi 12 = v 12 := by simp [vi, vh]
  have vl : vi 1 = v 1 := by simp [vi, vh]
  rw [vp, vl]
  by_cases hp : v 12 = v 1
  · rw [if_pos hp, min_eq_right (by omega)]
    have he : Function.update vi 12 (v 1) = vi := by rw [← hp, ← vp, Function.update_eq_self]
    rw [show Function.update (Function.update v 11 (v 11 / 2)) 7 (v 7 + 1) = vi by rfl, he]
    exact AReach.refl _
  · rw [if_neg hp, min_eq_left (by omega)]
    simpa only [astep_inc (show multARM .nextResult = _ from rfl), vp] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some .nextResult, vi, none)) ⟨mult_preconditions x _ vi none, bi⟩)

/-- All remaining multiplication columns halt with exactly their residual arithmetic
acceptance condition, within the required linear register bound.
Proof sketch. Induct on the number of remaining columns. The nested operand loops compute
one column, the zero-padded result read supplies its comparison bit, and parity success
halves the accumulator and advances the cursors. At the last column the saturated result
pointer tests excessive length and the accumulator tests final carry. -/
private lemma mult_columns_run (x a b c : List Bool)
    (encoded : x = pairEncode a (pairEncode b c)) (j : ℕ)
    (hj : j ≤ a.length + b.length) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (layout : v 1 = x.length ∧ v 2 = 2 * a.length + 2 ∧ v 4 = 2 * a.length ∧
      v 5 = 2 * a.length + 2 + 2 * b.length ∧ v 6 = a.length + b.length)
    (column : v 7 = j) (carry : v 11 = multCarry a b j)
    (result : v 12 = 2 * a.length + 2 + 2 * b.length + 2 + min j c.length) :
    MultHalt x (some .column, v, none) (decide (MultRemaining a b c j)) := by
  have size : x.length = 2 * a.length + 2 + 2 * b.length + 2 + c.length := by
    rw [encoded, length_pairEncode, length_pairEncode]; omega
  generalize hrem : a.length + b.length - j = remaining
  induction remaining using Nat.strong_induction_on generalizing j v with
  | h remaining ih =>
    by_cases done : j = a.length + b.length
    · apply AHalt.step ⟨mult_preconditions x .column v none, bound⟩
      simp only [astep_jeq (show multARM .column = _ from rfl), column, layout.2.2.2.2, if_pos done]
      have finish := mult_finish x v bound
      have exactTest : (v 12 = v 1 ∧ v 11 = 0) ↔ MultRemaining a b c j := by
        rw [result, layout.1, size, carry, done]
        simp only [MultRemaining]
        constructor
        · rintro ⟨hpos, hz⟩
          exact ⟨by omega, hz, fun i hi hn => by omega⟩
        · rintro ⟨hlen, hz, _⟩
          exact ⟨by omega, hz⟩
      simpa only [exactTest] using finish
    · have before : j < a.length + b.length := by omega
      let vs := Function.update (Function.update v 0 0) 8 0
      have bs : ∀ r, vs r ≤ 4 * (x.length + 1) :=
        register_update_le _ 8 _ 0 (register_update_le v 0 _ 0 bound (Nat.zero_le _)) (Nat.zero_le _)
      have reset : MultReach x (some .clearA, v, none) (some .outer, vs, none) := by
        apply AReach.step ⟨mult_preconditions x .clearA v none, bound⟩
        apply AReach.single
        exact ⟨mult_preconditions x .clearP _ none,
          register_update_le v 0 _ 0 bound (Nat.zero_le _)⟩
      have outer := mult_outer_loop x a b vs bs
        (by simp [vs, layout.2.2.1])
        (by simp [vs, layout.2.1, layout.2.2.2.1])
        (by simpa [vs, encoded] using (mult_addresses a b c).1)
        (by simpa [vs, layout.2.1, encoded] using (mult_addresses a b c).2.1)
        (by simp [vs]; omega)
        (by
          simp only [vs, Function.update_of_ne (by decide : (11 : Fin 13) ≠ 8),
            Function.update_of_ne (by decide : (11 : Fin 13) ≠ 0),
            Function.update_of_ne (by decide : (7 : Fin 13) ≠ 8),
            Function.update_of_ne (by decide : (7 : Fin 13) ≠ 0), Function.update_self,
            multRows_column, column, carry]
          have := multCarry_le a b j
          have := multColumn_le a b j
          omega)
      obtain ⟨ve, be, _, _, accum, frame, operands⟩ := outer
      have fixed (r : Fin 13) (safe : r ≠ 0 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 10 ∧ r ≠ 11) : ve r = v r := by
        rw [frame r safe.1 safe.2.1 safe.2.2.1 safe.2.2.2.1 safe.2.2.2.2]
        simp [vs, safe.1, safe.2.1]
      have e1 := fixed 1 (by decide)
      have e2 := fixed 2 (by decide)
      have e4 := fixed 4 (by decide)
      have e5 := fixed 5 (by decide)
      have e6 := fixed 6 (by decide)
      have e7 := fixed 7 (by decide)
      have e12 := fixed 12 (by decide)
      have esum : ve 11 = multCarry a b j + multColumn a b j := by
        simpa [vs, column, carry, multRows_column] using accum
      have elen : ve 1 = x.length := e1.trans layout.1
      have epos : ve 12 ≤ ve 1 := by rw [e12, result, elen, size]; omega
      have ebit : x.getD (ve 12) false = c.getD j false := by
        rw [e12, result, encoded, (mult_addresses a b c).2.2]
        by_cases hc : j ≤ c.length
        · rw [min_eq_left hc]
        · rw [min_eq_right (by omega)]
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : c.length ≤ j)]
      have reader := mult_result_read x ve be elen
      rw [ebit] at reader
      have parity := mult_parity x ve (c.getD j false) be
      by_cases agree : (c.getD j false).toNat = (multCarry a b j + multColumn a b j) % 2
      · rw [if_pos (by rwa [esum])] at parity
        have next := mult_next_column x ve be epos (by rw [e7, column]; omega)
        let vn := Function.update (Function.update (Function.update ve 11 (ve 11 / 2))
          7 (ve 7 + 1)) 12 (min (ve 12 + 1) (ve 1))
        have bn : ∀ r, vn r ≤ 4 * (x.length + 1) := by
          apply register_update_le _ 12 _ _
          · apply register_update_le _ 7 _ _
            · exact register_update_le ve 11 _ _ be ((Nat.div_le_self _ _).trans (be 11))
            · rw [e7, column]; omega
          · exact (Nat.min_le_right _ _).trans (be 1)
        have ln : vn 1 = x.length ∧ vn 2 = 2 * a.length + 2 ∧ vn 4 = 2 * a.length ∧
            vn 5 = 2 * a.length + 2 + 2 * b.length ∧ vn 6 = a.length + b.length := by
          simpa [vn, e1, e2, e4, e5, e6] using layout
        have jn : vn 7 = j + 1 := by simp [vn, e7, column]
        have cn : vn 11 = multCarry a b (j + 1) := by simp [vn, esum, multCarry]
        have rn : vn 12 = 2 * a.length + 2 + 2 * b.length + 2 + min (j + 1) c.length := by
          simp only [vn, Function.update_self]
          rw [e12, result, elen, size]
          omega
        have rest := ih (a.length + b.length - (j + 1)) (by omega)
          (j + 1) (by omega) vn bn ln jn cn rn rfl
        have exactNext : MultRemaining a b c j ↔ MultRemaining a b c (j + 1) := by
          rw [mult_remaining_step a b c j before]
          simp only [agree, true_and]
        rw [← exactNext] at rest
        apply AHalt.step ⟨mult_preconditions x .column v none, bound⟩
        simpa only [astep_jeq (show multARM .column = _ from rfl), column, layout.2.2.2.2,
          if_neg done] using
          reset.halt (operands.halt (reader.halt (parity.halt (next.halt rest))))
      · rw [if_neg (by rwa [esum])] at parity
        have reject : decide (MultRemaining a b c j) = false := by
          apply decide_eq_false
          rw [mult_remaining_step a b c j before]
          exact fun h => agree h.1
        rw [reject]
        apply AHalt.step ⟨mult_preconditions x .column v none, bound⟩
        simpa only [astep_jeq (show multARM .column = _ from rfl), column, layout.2.2.2.2,
          if_neg done] using
          reset.halt (operands.halt (reader.halt parity))

/-- Source register, shared-copy stage, and successful exit for each last-bit check. -/
private def multCanonSource (f : Fin 3) : Fin 13 := ![4, 5, 1] f

/-- Shared counting-copy stage selected by the canonical field. -/
private def multCanonCopy (f : Fin 3) : Fin 11 := if f = 0 then 5 else if f = 1 then 6 else 7

/-- Successful continuation selected by the canonical field. -/
private def multCanonNext (f : Fin 3) : MultState :=
  if f = 0 then .canonTest 1 else if f = 1 then .canonTest 2 else .copy 8 false

/-- The shared nonempty-field path reads its last physical bit. The first two fields are
strided by two and the third by one. The proof never decodes any field numerically.
Proof sketch. Clear the scratch pointer, invoke the received counting-copy loop, decrement
by the field stride, and make one input-bit query. All scratch values are at most the
source boundary, so the original register bound is preserved. -/
private lemma mult_last_bit (x : List Bool) (f : Fin 3) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) :
    MultReach x (some (.canonClear f), v, none)
      (some (if x.getD (v (multCanonSource f) - (if f = 2 then 1 else 2)) false
        then multCanonNext f else .answer false),
        Function.update v 0 (v (multCanonSource f) - (if f = 2 then 1 else 2)), none) := by
  have srcne : multCanonSource f ≠ 0 := (by decide : ∀ f, multCanonSource f ≠ 0) f
  have spec : multCopy (multCanonCopy f) = (0, multCanonSource f, .canonDown f false) :=
    (by decide : ∀ f, multCopy (multCanonCopy f) = (0, multCanonSource f, .canonDown f false)) f
  let va := Function.update v 0 0
  let vs := Function.update v 0 (v (multCanonSource f))
  let vd := Function.update v 0 (v (multCanonSource f) - (if f = 2 then 1 else 2))
  have ba : ∀ r, va r ≤ 4 * (x.length + 1) := register_update_le v 0 _ _ bound (Nat.zero_le _)
  have bs : ∀ r, vs r ≤ 4 * (x.length + 1) := register_update_le v 0 _ _ bound (bound _)
  have bd : ∀ r, vd r ≤ 4 * (x.length + 1) :=
    register_update_le v 0 _ _ bound ((Nat.sub_le _ _).trans (bound _))
  have copies : MultReach x (some (.copy (multCanonCopy f) false), va, none)
      (some (.canonDown f false), vs, none) := by
    simpa [spec, va, vs, srcne] using
      mult_copy x (multCanonCopy f) va ba (by simp [spec, va, srcne])
  have down : MultReach x (some (.canonDown f false), vs, none) (some (.canonRead f), vd, none) := by
    by_cases last : f = 2
    · simpa [astep_dec (show multARM (.canonDown 2 false) = _ from rfl), last, vs, vd] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some (.canonDown f false), vs, none)) ⟨mult_preconditions x _ vs none, bs⟩)
    · let vm := Function.update v 0 (v (multCanonSource f) - 1)
      have bm : ∀ r, vm r ≤ 4 * (x.length + 1) :=
        register_update_le v 0 _ _ bound ((Nat.sub_le _ _).trans (bound _))
      have first : MultReach x (some (.canonDown f false), vs, none)
          (some (.canonDown f true), vm, none) := by
        simpa [astep_dec (show multARM (.canonDown f false) = _ from rfl), last, vs, vm] using
          (AReach.single (A := multARM) (oracle := multOracle) (x := x)
            (a := (some (.canonDown f false), vs, none)) ⟨mult_preconditions x _ vs none, bs⟩)
      apply first.trans
      simpa [astep_dec (show multARM (.canonDown f true) = _ from rfl), last, vm, vd,
        Nat.sub_sub] using
        (AReach.single (A := multARM) (oracle := multOracle) (x := x)
          (a := (some (.canonDown f true), vm, none)) ⟨mult_preconditions x _ vm none, bm⟩)
  have read : MultReach x (some (.canonRead f), vd, none)
      (some (if x.getD (v (multCanonSource f) - (if f = 2 then 1 else 2)) false
        then multCanonNext f else .answer false), vd, none) := by
    simpa only [astep_call (show multARM (.canonRead f) = _ from rfl), vword_whole₁,
      (mult_queries x _).1,
      vd, Function.update_self, multCanonNext] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some (.canonRead f), vd, none)) ⟨mult_preconditions x _ vd none, bd⟩)
  apply AReach.step ⟨mult_preconditions x (.canonClear f) v none, bound⟩
  exact copies.trans (down.trans read)

/-- Canonical-field validation in continuation form. The only changed register is the
scratch pointer. Empty fields represent zero; nonempty fields are accepted exactly when
the physical last bit is true. The caller supplies the field-specific address equations. -/
private lemma mult_validate_field (x w : List Bool) (f : Fin 3) (v : Fin 13 → ℕ)
    (answer : Bool) (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (emptyStep : astep multARM multOracle x (some (.canonTest f), v, none) =
      (some (if w = [] then multCanonNext f else .canonClear f), v, none))
    (lastRead : w ≠ [] →
      x.getD (v (multCanonSource f) - (if f = 2 then 1 else 2)) false =
        w.getD (w.length - 1) false)
    (failure : ¬ Canon w → answer = false)
    (success : Canon w → ∀ u : Fin 13 → ℕ,
      (∀ r, u r ≤ 4 * (x.length + 1)) → (∀ r, r ≠ 0 → u r = v r) →
      MultHalt x (some (multCanonNext f), u, none) answer) :
    MultHalt x (some (.canonTest f), v, none) answer := by
  apply AHalt.step ⟨mult_preconditions x (.canonTest f) v none, bound⟩
  rw [emptyStep]
  by_cases empty : w = []
  · rw [if_pos empty]
    exact success (by simp [empty, Canon]) v bound (fun _ _ => rfl)
  · rw [if_neg empty]
    let u := Function.update v 0 (v (multCanonSource f) - (if f = 2 then 1 else 2))
    have bu : ∀ r, u r ≤ 4 * (x.length + 1) :=
      register_update_le v 0 _ _ bound ((Nat.sub_le _ _).trans (bound _))
    have frame : ∀ r, r ≠ 0 → u r = v r := fun r hr => Function.update_of_ne hr _ _
    have last := mult_last_bit x f v bound
    rw [lastRead empty] at last
    have canon : Canon w ↔ w.getD (w.length - 1) false = true := by
      rw [mult_canonical_last]
      simp only [List.length_eq_zero_iff, empty, false_or]
    by_cases valid : Canon w
    · rw [canon.mp valid, if_pos rfl] at last
      exact last.halt (success valid u bu frame)
    · have bit : w.getD (w.length - 1) false = false := by
        cases hb : w.getD (w.length - 1) false
        · rfl
        · exact False.elim (valid (canon.mpr hb))
      rw [bit, if_neg Bool.false_ne_true] at last
      rw [failure valid]
      exact last.halt (mult_return x false u bu)

/-- Phase-boundary metadata after shape parsing and before the three canonicality checks. -/
private structure MultReady (x a b c : List Bool) (v : Fin 13 → ℕ) : Prop where
  length : v 1 = x.length
  startB : v 2 = 2 * a.length + 2
  startC : v 3 = 2 * a.length + 2 + 2 * b.length + 2
  endA : v 4 = 2 * a.length
  endB : v 5 = 2 * a.length + 2 + 2 * b.length
  rounds : v 6 = a.length + b.length
  column : v 7 = 0
  carry : v 11 = 0
  result : v 12 = 0

/-- Canonicality checks preserve all metadata because they change only the scratch pointer. -/
private lemma mult_ready_frame {x a b c : List Bool} {v u : Fin 13 → ℕ}
    (ready : MultReady x a b c v) (frame : ∀ r, r ≠ 0 → u r = v r) :
    MultReady x a b c u :=
  ⟨(frame 1 (by decide)).trans ready.length, (frame 2 (by decide)).trans ready.startB,
    (frame 3 (by decide)).trans ready.startC, (frame 4 (by decide)).trans ready.endA,
    (frame 5 (by decide)).trans ready.endB, (frame 6 (by decide)).trans ready.rounds,
    (frame 7 (by decide)).trans ready.column, (frame 11 (by decide)).trans ready.carry,
    (frame 12 (by decide)).trans ready.result⟩

/-- The three canonicality checks followed by the proved column loop decide a parsed triple.
Proof sketch. Each field check calls the common last-bit path, accepting the empty word.
Failure excludes the existential language by pair injectivity. On success copy the result
start, run all columns from zero carry, and use the pure acceptance equivalence. -/
private lemma mult_canonical_run (x a b c : List Bool)
    (encoded : x = pairEncode a (pairEncode b c)) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1)) (ready : MultReady x a b c v) :
    MultHalt x (some (.canonTest 0), v, none) (decide (x ∈ multLang)) := by
  have size : x.length = 2 * a.length + 2 + 2 * b.length + 2 + c.length := by
    rw [encoded, length_pairEncode, length_pairEncode]; omega
  have member : x ∈ multLang ↔ Canon a ∧ Canon b ∧ Canon c ∧ MultRemaining a b c 0 := by
    simpa [encoded, MultRemaining] using mult_acceptance a b c
  apply mult_validate_field x a 0 v _ bound
  · simp [astep_jz (show multARM (.canonTest 0) = _ from rfl), multCanonNext, ready.endA,
      List.length_eq_zero_iff]
  · intro nonempty
    have pos : 0 < a.length := List.length_pos_iff.mpr nonempty
    change x.getD (v 4 - 2) false = _
    rw [ready.endA, show 2 * a.length - 2 = 2 * (a.length - 1) by omega, encoded]
    exact (mult_addresses a b c).1 _ (by omega)
  · intro invalid
    apply decide_eq_false
    intro h
    exact invalid (member.mp h).1
  · intro ha va ba fa
    have ra := mult_ready_frame ready fa
    change MultHalt x (some (.canonTest 1), va, none) _
    apply mult_validate_field x b 1 va _ ba
    · simp [astep_jeq (show multARM (.canonTest 1) = _ from rfl), multCanonNext, ra.endB, ra.startB,
        List.length_eq_zero_iff]
    · intro nonempty
      have pos : 0 < b.length := List.length_pos_iff.mpr nonempty
      change x.getD (va 5 - 2) false = _
      rw [ra.endB, show 2 * a.length + 2 + 2 * b.length - 2 =
        2 * a.length + 2 + 2 * (b.length - 1) by omega, encoded]
      exact (mult_addresses a b c).2.1 _ (by omega)
    · intro invalid
      apply decide_eq_false
      intro h
      exact invalid (member.mp h).2.1
    · intro hb vb bb fb
      have rb := mult_ready_frame ra fb
      change MultHalt x (some (.canonTest 2), vb, none) _
      apply mult_validate_field x c 2 vb _ bb
      · have test : (vb 3 = vb 1) ↔ c = [] := by
          rw [rb.startC, rb.length, size]
          simp
        simp only [astep_jeq (show multARM (.canonTest 2) = _ from rfl), multCanonNext]
        simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
          ↓reduceIte, test]
      · intro nonempty
        have pos : 0 < c.length := List.length_pos_iff.mpr nonempty
        change x.getD (vb 1 - 1) false = _
        rw [rb.length, size, show 2 * a.length + 2 + 2 * b.length + 2 + c.length - 1 =
          2 * a.length + 2 + 2 * b.length + 2 + (c.length - 1) by omega, encoded]
        exact (mult_addresses a b c).2.2 _
      · intro invalid
        apply decide_eq_false
        intro h
        exact invalid (member.mp h).2.2.1
      · intro hc vc bc fc
        have rc := mult_ready_frame rb fc
        change MultHalt x (some (.copy 8 false), vc, none) _
        have start := mult_copy x 8 vc bc (by simp [multCopy, rc.result])
        let vd := Function.update vc 12 (vc 3)
        have bd : ∀ r, vd r ≤ 4 * (x.length + 1) := register_update_le vc 12 _ _ bc (bc 3)
        have layout : vd 1 = x.length ∧ vd 2 = 2 * a.length + 2 ∧ vd 4 = 2 * a.length ∧
            vd 5 = 2 * a.length + 2 + 2 * b.length ∧ vd 6 = a.length + b.length := by
          simpa [vd] using ⟨rc.length, rc.startB, rc.endA, rc.endB, rc.rounds⟩
        have columns := mult_columns_run x a b c encoded 0 (Nat.zero_le _) vd bd layout
          (by simpa [vd] using rc.column) (by simpa [vd, multCarry] using rc.carry)
          (by simpa [vd] using rc.startC)
        have acceptance : (x ∈ multLang) ↔ MultRemaining a b c 0 := by
          rw [member]
          simp only [ha, hb, hc, true_and]
        rw [← acceptance] at columns
        apply start.halt
        exact columns

/-- Two consecutive decrements share one bounded path argument. This private arithmetic
fragment is a promotion candidate for the shared input-access layer. -/
private lemma mult_sub_two (x : List Bool) (v : Fin 13 → ℕ) (r : Fin 13)
    (labels : Bool → MultState) (done : MultState)
    (code₀ : multARM (labels false) = .dec r (labels true))
    (code₁ : multARM (labels true) = .dec r done)
    (bound : ∀ s, v s ≤ 4 * (x.length + 1)) :
    MultReach x (some (labels false), v, none)
      (some done, Function.update v r (v r - 2), none) := by
  apply AReach.step ⟨mult_preconditions x _ v none, bound⟩
  rw [astep_dec code₀]
  have nextBound := register_update_le v r (4 * (x.length + 1)) (v r - 1) bound
    ((Nat.sub_le _ _).trans (bound r))
  simpa only [astep_dec code₁, Function.update_self, Function.update_idem, Nat.sub_sub,
    show (1 : ℕ) + 1 = 2 by rfl] using
    (AReach.single (A := multARM) (oracle := multOracle) (x := x)
      (a := (some (labels true), Function.update v r (v r - 1), none))
      ⟨mult_preconditions x _ _ none, nextBound⟩)

/-- Parsed boundaries are converted to operand ends and the number of product columns.
Proof sketch. Shared copies preserve the two starts. Two decrements remove each separator;
halving the second start and subtracting two gives the sum of operand lengths. Every
arithmetic operation decreases a copied boundary. The canonicality/column proof then applies. -/
private lemma mult_prepare_run (x a b c : List Bool)
    (encoded : x = pairEncode a (pairEncode b c)) (v : Fin 13 → ℕ)
    (bound : ∀ r, v r ≤ 4 * (x.length + 1))
    (len : v 1 = x.length) (startB : v 2 = 2 * a.length + 2)
    (startC : v 3 = 2 * a.length + 2 + 2 * b.length + 2)
    (a0 : v 4 = 0) (b0 : v 5 = 0) (n0 : v 6 = 0)
    (j0 : v 7 = 0) (carry0 : v 11 = 0) (result0 : v 12 = 0) :
    MultHalt x (some (.copy 2 false), v, none) (decide (x ∈ multLang)) := by
  let va := Function.update v 4 (2 * a.length)
  let vb := Function.update va 5 (2 * a.length + 2 + 2 * b.length)
  let vn := Function.update vb 6 (a.length + b.length)
  have ba : ∀ r, va r ≤ 4 * (x.length + 1) := by
    apply register_update_le v 4 _ _ bound
    have := bound 2; rw [startB] at this; omega
  have bb : ∀ r, vb r ≤ 4 * (x.length + 1) := by
    apply register_update_le va 5 _ _ ba
    have := bound 3; rw [startC] at this; omega
  have bn : ∀ r, vn r ≤ 4 * (x.length + 1) := by
    apply register_update_le vb 6 _ _ bb
    have := bound 3; rw [startC] at this; omega
  have cpA := mult_copy x 2 v bound (by simp [multCopy, a0])
  have bca : ∀ r, Function.update v 4 (v 2) r ≤ 4 * (x.length + 1) :=
    register_update_le v 4 _ _ bound (bound 2)
  have subA : MultReach x (some (.endDown false false), Function.update v 4 (v 2), none)
      (some (.copy 3 false), va, none) := by
    simpa [va, startB] using mult_sub_two x (Function.update v 4 (v 2)) 4
      (.endDown false) (.copy 3 false) rfl rfl bca
  have cpB := mult_copy x 3 va ba (by simp [multCopy, va, b0])
  have bcb : ∀ r, Function.update va 5 (va 3) r ≤ 4 * (x.length + 1) :=
    register_update_le va 5 _ _ ba (ba 3)
  have subB : MultReach x (some (.endDown true false), Function.update va 5 (va 3), none)
      (some (.copy 4 false), vb, none) := by
    simpa [vb, va, startC] using mult_sub_two x (Function.update va 5 (va 3)) 5
      (.endDown true) (.copy 4 false) rfl rfl bcb
  have cpN := mult_copy x 4 vb bb (by simp [multCopy, vb, va, n0])
  let vc := Function.update vb 6 (vb 3)
  let vh := Function.update vb 6 (vb 3 / 2)
  have bc : ∀ r, vc r ≤ 4 * (x.length + 1) := register_update_le vb 6 _ _ bb (bb 3)
  have bh : ∀ r, vh r ≤ 4 * (x.length + 1) :=
    register_update_le vb 6 _ _ bb ((Nat.div_le_self _ _).trans (bb 3))
  have half : MultReach x (some .countHalf, vc, none) (some (.countDown false), vh, none) := by
    simpa [astep_half (show multARM .countHalf = _ from rfl), vc, vh] using
      (AReach.single (A := multARM) (oracle := multOracle) (x := x)
        (a := (some .countHalf, vc, none)) ⟨mult_preconditions x _ vc none, bc⟩)
  have arithmetic : vb 3 / 2 - 2 = a.length + b.length := by simp [vb, va, startC]; omega
  have subN : MultReach x (some (.countDown false), vh, none) (some (.canonTest 0), vn, none) := by
    simpa only [vh, Function.update_self, Function.update_idem, arithmetic, vn] using
      mult_sub_two x vh 6 .countDown (.canonTest 0) rfl rfl bh
  have ready : MultReady x a b c vn := by
    constructor <;> simp [vn, vb, va, len, startB, startC, j0, carry0, result0]
  have finish := mult_canonical_run x a b c encoded vn bn ready
  exact cpA.halt (subA.halt (cpB.halt (subB.halt (cpN.halt (half.halt (subN.halt finish))))))

/-- A failed outer or inner pair decode excludes every genuine multiplication triple. -/
private lemma mult_bad_decode (x : List Bool)
    (bad : (pairDecode x).bind (fun p => pairDecode p.2) = none) : x ∉ multLang := by
  rintro ⟨u, v, rfl⟩
  simp only [pairDecode_pairEncode, Option.bind_some, reduceCtorEq] at bad

/-- The complete all-input bounded halting theorem for the multiplication ARM.
Proof sketch. Count the physical input with the public length fragment and validate both
aligned pairs with the public shape fragment. Either failure rejects a malformed triple.
On success, shared copies retain the two suffix starts; separator arithmetic prepares the
metadata and the proved canonicality/column construction supplies the answer. -/
private lemma mult_run (x : List Bool) :
    MultHalt x (some .lengthTest, fun _ => 0, none) (decide (x ∈ multLang)) := by
  let vl : Fin 13 → ℕ := Function.update (fun _ => 0) 1 x.length
  have bl : ∀ r, vl r ≤ 4 * (x.length + 1) :=
    register_update_le (fun _ => 0) 1 _ _ (fun _ => Nat.zero_le _) (by omega)
  have length : MultReach x (some .lengthTest, fun _ => 0, none)
      (some (.pairTest false), vl, none) :=
    inputLength_loop multARM multOracle x 1 1 .lengthTest .lengthInc (.pairTest false)
      rfl rfl (fun i _ => (mult_queries x i).2) _ (by omega) (fun _ => 0)
      (fun _ => Nat.zero_le _) (Nat.zero_le _)
  have outer := mult_scan x x false vl bl (by simp [vl]) (by simp [vl])
  cases parsed : pairDecode x with
  | none =>
    rw [parsed] at outer
    obtain ⟨t, ht, path⟩ := outer
    have lastBound : ∀ r, Function.update vl 0 (vl 0 + t) r ≤ 4 * (x.length + 1) := by
      apply register_update_le vl 0 _ _ bl
      simp [vl]; omega
    have reject := mult_bad_decode x (by simp [parsed])
    simpa only [reject, decide_false] using length.halt (path.halt (mult_return x false _ lastBound))
  | some fields =>
    rcases fields with ⟨a, tail⟩
    have eqx := eq_pairEncode_of_pairDecode x a tail parsed
    have outerSize : x.length = 2 * a.length + 2 + tail.length := by rw [eqx, length_pairEncode]
    let vs := Function.update vl 0 (2 * a.length + 2)
    let vb := Function.update vs 2 (2 * a.length + 2)
    have bs : ∀ r, vs r ≤ 4 * (x.length + 1) := register_update_le vl 0 _ _ bl (by omega)
    have bb : ∀ r, vb r ≤ 4 * (x.length + 1) := register_update_le vs 2 _ _ bs (by omega)
    have outerPath : MultReach x (some (.pairTest false), vl, none)
        (some (.copy 0 false), vs, none) := by simpa [parsed, vl, vs] using outer
    have saveB : MultReach x (some (.copy 0 false), vs, none)
        (some (.pairTest true), vb, none) := by
      simpa [multCopy, vs, vb, vl] using mult_copy x 0 vs bs (by simp [multCopy, vs, vl])
    have inner := mult_scan x tail true vb bb (by simp [vb, vs, vl]; omega) (by
      intro i hi
      change x.getD (2 * a.length + 2 + i) false = tail.getD i false
      rw [eqx, pairEncode_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      congr 1
      omega)
    cases nested : pairDecode tail with
    | none =>
      rw [nested] at inner
      obtain ⟨t, ht, path⟩ := inner
      have lastBound : ∀ r, Function.update vb 0 (vb 0 + t) r ≤ 4 * (x.length + 1) := by
        apply register_update_le vb 0 _ _ bb
        simp [vb, vs, vl]; omega
      have reject := mult_bad_decode x (by simp [parsed, nested])
      simpa only [reject, decide_false] using
        length.halt (outerPath.halt (saveB.halt (path.halt (mult_return x false _ lastBound))))
    | some fields =>
      rcases fields with ⟨b, c⟩
      have eqtail := eq_pairEncode_of_pairDecode tail b c nested
      have encoded : x = pairEncode a (pairEncode b c) := by rw [eqx, eqtail]
      have size : x.length = 2 * a.length + 2 + 2 * b.length + 2 + c.length := by
        rw [encoded, length_pairEncode, length_pairEncode]; omega
      let vc := Function.update vb 0 (2 * a.length + 2 + 2 * b.length + 2)
      let vd := Function.update vc 3 (2 * a.length + 2 + 2 * b.length + 2)
      have bc : ∀ r, vc r ≤ 4 * (x.length + 1) := register_update_le vb 0 _ _ bb (by omega)
      have bd : ∀ r, vd r ≤ 4 * (x.length + 1) := register_update_le vc 3 _ _ bc (by omega)
      have innerPath : MultReach x (some (.pairTest true), vb, none)
          (some (.copy 1 false), vc, none) := by
        simpa [nested, vc, vb, vs, vl, Nat.add_assoc] using inner
      have saveC : MultReach x (some (.copy 1 false), vc, none)
          (some (.copy 2 false), vd, none) := by
        simpa [multCopy, vc, vd] using mult_copy x 1 vc bc (by simp [multCopy, vc, vb, vs, vl])
      have prepared : MultHalt x (some (.copy 2 false), vd, none) (decide (x ∈ multLang)) := by
        apply mult_prepare_run x a b c encoded vd bd <;> simp [vd, vc, vb, vs, vl]
      exact length.halt (outerPath.halt (saveB.halt (innerPath.halt (saveC.halt prepared))))

/-- **Multiplication verifies in logarithmic space** ([AB09, Example 4.7];
proved — phase P4.4): the grade-school method checks the third
component bit by bit with carry and index counters only.

**Proof sketch.** The verifier computes each bit of `a · b` on demand:
bit `j` of the product is determined by the column sums
`∑_{p+q=j'} a_p · b_q` for `j' ≤ j` propagated through the carry — maintain
the carry (of `O(logSpace n)` bits, since a column sum is at most the input
length) and two index counters, re-reading `a`'s and `b`'s bits from the
input by position arithmetic on the nested pair layout (through `whole`-mode
calls to the input-access languages `Complexity.inputBitLang` and
`Complexity.inputLenLang` of phase P4.4b; the received
`Machines/Parse2`/`ParseCmp` toolkit reads only unary-first inputs
`⟨1ⁿ, ⟨u, w⟩⟩` and does not apply); compare each computed bit against the
third component's bit and reject on mismatch or malformed shape; accept when
every column through `|a| + |b|` matches (missing result bits read as `0`, a
longer result field rejected) and no carry remains. Registers: carry, two
indices, a column cursor — `O(logSpace n)` cells; assembled by the received
`arm_decides_poly`. Fill obligations, named: the column-sum/carry invariant;
the position arithmetic into the nested pairs; the shape validator; the
`DecidesInSpace` packaging. (Sketch prose corrected at phase P4.4b; the
statement is unchanged.) -/
theorem multLang_mem_LOGSPACE : multLang ∈ LOGSPACE := by
  refine arm_decides_poly multARM .lengthTest ![inputBitLang, inputLenLang] ?_ 4 1 ?_
  · intro i
    rcases i with ⟨i, hi⟩
    have cases : i = 0 ∨ i = 1 := by omega
    rcases cases with rfl | rfl
    · exact inputBitLang_mem
    · exact inputLenLang_mem
  · intro x
    simpa only [pow_one, multOracle, indicator_eq_decide] using mult_run x

end Complexity
```

## ===== TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PreimageHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reshaping implicit queries

To compose implicitly logspace computable functions [AB09, Lemma 4.17's proof], a query
`⟨x, bits i⟩` about `g (f x)` is reshaped into the query `⟨f x, bits i⟩` about `g`. This is
`Complexity.compQ f`, and it is itself implicitly logspace computable. Both query languages of
`g ∘ f` are then preimages of `g`'s along it (`Complexity.mem_indexLang_compQ_iff`), hence in
`L` by `Complexity.mem_LOGSPACE_preimage`.

Deciding `compQ f`'s own languages needs `f`'s queries at `⟨x, bits j⟩`. An abstract register
machine on the host `⟨⟨x, bits i⟩, bits p⟩` can only present `⟨⟨⟨x, bits i⟩, bits p⟩, bits j⟩`
(a `whole`-mode call). The index-dropping map `Complexity.dropIdx` takes
`⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`; applied twice it recovers `⟨x, bits j⟩`.

Phase P4.4b of `AroraBarakChapters3-4Plan.md`; see `audits/ch4-p44-resolutions-addendum.md`.

## Main definitions

* `Complexity.dropIdx` — `⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`, and `[]` off that shape.
* `Complexity.compQ` — `⟨x, b⟩ ↦ ⟨f x, b⟩` for canonical `b`, and `[]` otherwise.

## Main results

* `Complexity.dropIdx_pairEncode`, `Complexity.dropIdx_length_le` — the map on nested pairs;
  its length bound.
* `Complexity.compQ_pairEncode`, `Complexity.mem_indexLang_compQ_iff`,
  `Complexity.compQ_length_le` — the map on queries; the preimage identity; the length bound.
* `Complexity.implicitlyLogspaceComputable_dropIdx`,
  `Complexity.ImplicitlyLogspaceComputable.compQ` — both maps are implicitly logspace
  computable (proved; phase-P4.4b statements).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Definition 4.16, Lemma 4.17 and its proof.)
-/

namespace Complexity

open Turing

/-- **Dropping the middle index**: `⟨⟨w, b⟩, b'⟩ ↦ ⟨w, b'⟩`, and `[]` on words not of that
shape. -/
def dropIdx (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (u, b') =>
    match pairDecode u with
    | some (w, _) => pairEncode w b'
    | none => []
  | none => []

/-- `dropIdx` on a nested pair. -/
theorem dropIdx_pairEncode (w b b' : List Bool) :
    dropIdx (pairEncode (pairEncode w b) b') = pairEncode w b' := by
  simp [dropIdx, pairDecode_pairEncode]

/-- `dropIdx` never lengthens a word. -/
theorem dropIdx_length_le (z : List Bool) : (dropIdx z).length ≤ z.length := by
  unfold dropIdx
  split
  · rename_i u b' hz
    split
    · rename_i w b hu
      rw [eq_pairEncode_of_pairDecode _ _ _ hz, eq_pairEncode_of_pairDecode _ _ _ hu]
      simp only [length_pairEncode]
      omega
    · simp
  · simp

/-- **The query reshaping of a composition**: `⟨x, b⟩ ↦ ⟨f x, b⟩` when `b` is a canonical
binary word (some `Nat.bits i`), and `[]` otherwise. -/
def compQ (f : List Bool → List Bool) (w : List Bool) : List Bool :=
  match pairDecode w with
  | some (x, b) => if Nat.bits (LogProg.bitsVal b) = b then pairEncode (f x) b else []
  | none => []

/-- `compQ f` on a genuine query. -/
theorem compQ_pairEncode (f : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    compQ f (pairEncode x (Nat.bits i)) = pairEncode (f x) (Nat.bits i) := by
  simp [compQ, pairDecode_pairEncode, LogProg.bitsVal_bits]

/-- **The preimage identity of composition**: a word is in `{⟨x, i⟩ | p (f x) i}` iff its
reshaping is in `{⟨y, i⟩ | p y i}`. Malformed and non-canonical queries go to `[]`, which no
index language contains. -/
theorem mem_indexLang_compQ_iff (f : List Bool → List Bool) (p : List Bool → ℕ → Prop)
    (w : List Bool) :
    w ∈ indexLang (fun x i => p (f x) i) ↔ compQ f w ∈ indexLang p := by
  constructor
  · rintro ⟨x, i, rfl, hp⟩
    exact ⟨f x, i, compQ_pairEncode f x i, hp⟩
  · rintro ⟨y, i, h, hp⟩
    unfold compQ at h
    split at h
    · rename_i x b hw
      split_ifs at h with hb
      · have := pairEncode_injective (a₁ := (f x, b)) (a₂ := (y, Nat.bits i)) h
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        exact ⟨x, i, eq_pairEncode_of_pairDecode _ _ _ hw, hp⟩
      · exact absurd h.symm (pairEncode_ne_nil _ _)
    · exact absurd h.symm (pairEncode_ne_nil _ _)

/-- `compQ f` is polynomially bounded when `f` is: `|compQ f w| ≤ (2C + 3)(|w| + 1)^{c+1}`
from `|f x| ≤ C (|x| + 1)^c`. -/
theorem compQ_length_le {f : List Bool → List Bool} {C c : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ c) (w : List Bool) :
    (compQ f w).length ≤ (2 * C + 3) * (w.length + 1) ^ (c + 1) := by
  unfold compQ
  split
  · rename_i x b hw
    split_ifs
    · have hw' := eq_pairEncode_of_pairDecode _ _ _ hw
      have hl : w.length = 2 * x.length + 2 + b.length := by rw [hw', length_pairEncode]
      have e1 : (w.length + 1) ^ c ≤ (w.length + 1) ^ (c + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have e2 : w.length + 1 ≤ (w.length + 1) ^ (c + 1) := by
        calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      have e3 : (f x).length ≤ C * (w.length + 1) ^ c :=
        (hf x).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      have e4 : C * (w.length + 1) ^ c ≤ C * (w.length + 1) ^ (c + 1) :=
        Nat.mul_le_mul_left _ e1
      rw [length_pairEncode]
      have e5 : (2 * C + 3) * (w.length + 1) ^ (c + 1) =
          2 * (C * (w.length + 1) ^ (c + 1)) + 3 * (w.length + 1) ^ (c + 1) := by ring
      omega
    · simp
  · simp

/-- The kept prefix of `dropIdx` is read at stride four in its paired query host.
The discarded middle field and the retained suffix are arbitrary words.

**Proof sketch.** The two enclosing first-field encodings each double addresses. Below
the separator of the innermost pair, changing its second field does not change a bit. -/
private lemma dropIdx_prefix_address (w b b' tail : List Bool) (j : ℕ)
    (hj : j < 2 * w.length + 2) :
    (dropIdx (pairEncode (pairEncode w b) b')).getD j false =
      (pairEncode (pairEncode (pairEncode w b) b') tail).getD (4 * j) false := by
  have hu := length_pairEncode w b
  have hz := length_pairEncode (pairEncode w b) b'
  have h₁ : (pairEncode (pairEncode (pairEncode w b) b') tail).getD (4 * j) false =
      (pairEncode (pairEncode w b) b').getD (2 * j) false := by
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  have h₂ : (pairEncode (pairEncode w b) b').getD (2 * j) false =
      (pairEncode w b).getD j false := by
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  rw [h₁, h₂, dropIdx_pairEncode, pairEncode_getD, pairEncode_getD]
  split_ifs <;> first | rfl | omega

/-- A retained suffix bit is read after the doubled outer separator. This address is
used only within the suffix; an out-of-range query must be rejected before making it.

**Proof sketch.** Remove the host's outer doubling, then the discarded pair's doubled
first field and separator. The remaining address is exactly the suffix index. -/
private lemma dropIdx_suffix_address (w b b' tail : List Bool) (j : ℕ) (hj : j < b'.length) :
    (dropIdx (pairEncode (pairEncode w b) b')).getD (2 * w.length + 2 + j) false =
      (pairEncode (pairEncode (pairEncode w b) b') tail).getD
        (4 * (pairEncode w b).length + 4 + 2 * j) false := by
  have hz := length_pairEncode (pairEncode w b) b'
  have h₁ : (pairEncode (pairEncode (pairEncode w b) b') tail).getD
        (4 * (pairEncode w b).length + 4 + 2 * j) false =
      (pairEncode (pairEncode w b) b').getD (2 * (pairEncode w b).length + 2 + j) false := by
    rw [pairEncode_getD, if_pos (by omega)]
    congr 1
    omega
  rw [h₁, dropIdx_pairEncode, pairEncode_getD, pairEncode_getD]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

/-- Passing a binary-width check bounds the decoded value by twice the cap, including a
zero cap. This also bounds every partial value in a most-significant-bit-first decoder.

**Proof sketch.** The value is below `2 ^ size n`. For positive `n`, its top binary place
is at most `n`, hence `2 ^ size n ≤ 2*n`; at zero both canonical representations are empty. -/
private lemma query_index_bound (r n : ℕ)
    (hwidth : (Nat.bits r).length ≤ (Nat.bits n).length) : r ≤ 2 * n := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len] at hwidth
  have hr := Nat.size_le.mp hwidth
  by_cases hn : n = 0
  · subst n
    simp only [Nat.size_zero, pow_zero] at hr
    omega
  · have hs : 0 < n.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hn)
    have htop : 2 ^ (n.size - 1) ≤ n := Nat.lt_size.mp (by omega)
    have hpow : 2 ^ n.size = 2 * 2 ^ (n.size - 1) := by
      conv_lhs => rw [show n.size = (n.size - 1) + 1 by omega, pow_succ]
      omega
    rw [hpow] at hr
    omega

/-- Discarding low-order digits cannot increase a binary word's value. -/
private lemma query_suffix_value_le (w : List Bool) (j : ℕ) :
    LogProg.bitsVal (w.drop j) ≤ LogProg.bitsVal w := by
  induction j generalizing w with
  | zero => simp
  | succ j ih =>
    cases w with
    | nil => simp [LogProg.bitsVal]
    | cons b w =>
      have h := ih w
      simp only [List.drop_succ_cons, LogProg.bitsVal]
      omega

/-- The width test bounds every accumulator of the reverse tail scan before decoding it.
Canonicality is required only of the query index, never of `dropIdx`'s payload fields. -/
private lemma query_accumulator_bound (w : List Bool) (n j : ℕ) (hc : LogProg.Canon w)
    (hwidth : w.length ≤ (Nat.bits n).length) : LogProg.bitsVal (w.drop j) ≤ 2 * n := by
  apply (query_suffix_value_le w j).trans
  apply query_index_bound
  simpa only [← LogProg.canon_eq_bits w hc] using hwidth

/-- The canonical-index length overflow test makes both queries false before its
numerical value is accumulated. -/
private lemma dropIdx_query_overflow (z : List Bool) (r : ℕ)
    (hlarge : (Nat.bits ((pairEncode z (Nat.bits r)).length)).length < (Nat.bits r).length) :
    (dropIdx z).getD r false = false ∧ ¬ r < (dropIdx z).length := by
  have hr : (pairEncode z (Nat.bits r)).length < r := by
    by_contra h
    have hb := LogProg.length_bits_mono (Nat.le_of_not_gt h)
    omega
  have hz := length_pairEncode z (Nat.bits r)
  have hd := dropIdx_length_le z
  have hout : (dropIdx z).length ≤ r := by omega
  exact ⟨by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hout], by omega⟩

/-! ## The bounded index-dropping ARM -/

open LogProg Classical

/-- Finite control of the one index-dropping ARM. The mode parameter selects bit or length
answers only at a successful lookup. Registers hold the physical pointer, host end,
first-field end, retained-suffix start, inner-field end, prefix end, query, scratch/candidate,
and query-tail start, in that order. -/
private inductive DropState where
  | lengthTest | lengthInc
  | copy (stage : Fin 8) (bump : Bool)
  | scan (layer : Fin 3) | first (layer : Fin 3)
  | second (layer : Fin 3) (bit : Bool) | readSecond (layer : Fin 3) (bit : Bool)
  | scanInc (layer : Fin 3) (choice : Fin 4) (step : Fin 4)
  | tailTest (last : Bool) | tailCheck | tailRead | tailHalf (bit : Bool) | tailInc (bit : Bool)
  | tailDone | clearPtr (stage : Fin 5)
  | zDec (step : Fin 2) | uDec (step : Fin 4)
  | decode | decodeDown | decodeRead | decodeCopy (bit : Bool) | decodeCopyInc (bit : Bool)
  | decodeClear (bit : Bool) | decodeScale (bit : Bool) | decodeTake (bit : Bool)
  | decodeInc (bit : Bool) (second : Bool) | decodeAdd (bit : Bool)
  | seek (suffix : Bool) | matchIndex (suffix : Bool) | nextIndex (suffix : Bool)
  | walk (suffix : Bool) (step : Fin 4) | hit | answer (bit : Bool)
  deriving DecidableEq, Fintype

/-- Each copy stage names its destination, source, and continuation. -/
private def dropCopy : Fin 8 → Fin 9 × Fin 9 × DropState
  | 0 => (8, 0, .copy 1 false)
  | 1 => (7, 1, .tailTest true)
  | 2 => (0, 1, .decode)
  | 3 => (2, 8, .zDec 0)
  | 4 => (3, 0, .copy 5 false)
  | 5 => (4, 0, .uDec 0)
  | 6 => (5, 0, .clearPtr 3)
  | 7 => (0, 3, .seek true)

/-- The three pair scans read the host, its first field, and that field's first field. -/
private def dropStride (layer : Fin 3) : ℕ := ![1, 2, 4] layer

/-- End registers for those scans, all in physical host coordinates. -/
private def dropLimit (layer : Fin 3) : Fin 9 := ![1, 2, 4] layer

/-- A successful scan stores its boundary before the next phase. -/
private def dropScanDone (layer : Fin 3) : DropState :=
  .copy (![0, 4, 6] layer) false

/-- Shared finite increment chains for the received aligned scan. -/
private def dropAdvance (layer : Fin 3) (choice : Fin 4) (i : ℕ) : DropState :=
  if h : i < dropStride layer then .scanInc layer choice ⟨i, by
    have : dropStride layer ≤ 4 := (by decide : ∀ l, dropStride l ≤ 4) layer
    omega⟩
  else ![.second layer false, .second layer true, .scan layer, dropScanDone layer] choice

/-- A one-cell advance of the outer query tail. -/
private def dropTailAdvance (b : Bool) (i : ℕ) : DropState :=
  if i = 0 then .tailInc b else .tailTest b

/-- Two increments implement the decoder's doubling transfer. -/
private def dropDecodeAdvance (b : Bool) (i : ℕ) : DropState :=
  if i = 0 then .decodeInc b false else if i = 1 then .decodeInc b true else .decodeScale b

/-- Lookup walks use stride four in the kept prefix and stride two in the retained suffix. -/
private def dropWalk (suffix : Bool) (i : ℕ) : DropState :=
  if h : i < (if suffix then 2 else 4) then
    .walk suffix ⟨i, by
      cases suffix with
      | false => exact h
      | true => have : i < 2 := h; omega⟩
  else .seek suffix

/-- The complete index-dropping table, assembled from the bounded shared fragments.
Only the outer query tail is required to be canonical. The two payloads scanned inside
its first field are arbitrary words. -/
private def dropARM (lengthMode : Bool) : ARM 9 2 DropState
  | .lengthTest => .call 1 .whole [1] .lengthInc (.scan 0)
  | .lengthInc => .inc 1 .lengthTest
  | .copy s false => .jeq (dropCopy s).1 (dropCopy s).2.1 (dropCopy s).2.2 (.copy s true)
  | .copy s true => .inc (dropCopy s).1 (.copy s false)
  | .scan layer => .jeq 0 (dropLimit layer) (.answer false) (.first layer)
  | .first layer => .call 0 .whole [0] (dropAdvance layer 1 0) (dropAdvance layer 0 0)
  | .second layer b => .jeq 0 (dropLimit layer) (.answer false) (.readSecond layer b)
  | .readSecond layer b => .call 0 .whole [0]
      (if b then dropAdvance layer 2 0 else dropAdvance layer 3 0)
      (if b then .answer false else dropAdvance layer 2 0)
  | .scanInc layer choice i => .inc 0 (dropAdvance layer choice (i.val + 1))
  | .tailTest b => .jeq 0 1 (if b then .tailDone else .answer false) .tailCheck
  | .tailCheck => .jz 7 (.answer false) .tailRead
  | .tailRead => .call 0 .whole [0] (.tailHalf true) (.tailHalf false)
  | .tailHalf b => .half 7 (.tailInc b)
  | .tailInc b => .inc 0 (.tailTest b)
  | .tailDone => .clr 7 (.clearPtr 0)
  | .clearPtr s => .clr 0 (![.copy 2 false, .scan 1, .scan 2, .seek false, .copy 7 false] s)
  | .zDec i => .dec 2 (if i = 0 then .zDec 1 else .clearPtr 1)
  | .uDec i => .dec 4 (if h : i.val + 1 < 4 then .uDec ⟨i.val + 1, h⟩ else .clearPtr 2)
  | .decode => .jeq 0 8 (.copy 3 false) .decodeDown
  | .decodeDown => .dec 0 .decodeRead
  | .decodeRead => .call 0 .whole [0] (.decodeCopy true) (.decodeCopy false)
  | .decodeCopy b => .jeq 7 6 (.decodeClear b) (.decodeCopyInc b)
  | .decodeCopyInc b => .inc 7 (.decodeCopy b)
  | .decodeClear b => .clr 6 (.decodeScale b)
  | .decodeScale b => .jz 7 (.decodeAdd b) (.decodeTake b)
  | .decodeTake b => .dec 7 (.decodeInc b false)
  | .decodeInc b false => .inc 6 (.decodeInc b true)
  | .decodeInc b true => .inc 6 (.decodeScale b)
  | .decodeAdd b => if b then .inc 6 .decode else .jz 7 .decode .decode
  | .seek suffix => .jeq 0 (if suffix then 2 else 5)
      (if suffix then .answer false else .clearPtr 4) (.matchIndex suffix)
  | .matchIndex suffix => .jeq 7 6 .hit (.nextIndex suffix)
  | .nextIndex suffix => .inc 7 (dropWalk suffix 0)
  | .walk suffix i => .inc 0 (dropWalk suffix (i.val + 1))
  | .hit => if lengthMode then .ret true else .call 0 .whole [0] (.answer true) (.answer false)
  | .answer b => .ret b

/-- The access bank is independent of the mode. -/
private def dropBank : Fin 2 → Language Bool := ![inputBitLang, inputLenLang]

/-- Both modes use the same language expression and the same table. -/
private def dropLang (lengthMode : Bool) : Language Bool :=
  indexLang fun z q => if lengthMode then q < (dropIdx z).length else (dropIdx z).getD q false = true

/-- Every reachable instruction's syntactic side conditions already hold for this table.
There are no format-specific input instructions, and every call has one argument. -/
private lemma drop_preS (mode : Bool) (h : List Bool) (c : AConf 9 DropState) :
    PreS (dropARM mode) h c := by
  rcases c with ⟨l, v, ans⟩
  cases l with
  | none => trivial
  | some l =>
    cases l <;> simp only [PreS, dropARM] <;> try decide
    case copy stage bump =>
      cases bump
      · exact (by decide : ∀ s, (dropCopy s).1 ≠ (dropCopy s).2.1) stage
      · trivial
    case scan layer => exact (by decide : ∀ l, (0 : Fin 9) ≠ dropLimit l) layer
    case second layer bit => exact (by decide : ∀ l, (0 : Fin 9) ≠ dropLimit l) layer
    case decodeAdd bit => cases bit <;> trivial
    case seek suffix => cases suffix <;> decide
    case decodeInc bit second => cases second <;> trivial
    case hit => cases mode <;> simp

/-- Truthful calls to the fixed two-language access bank. -/
private noncomputable def dropOracle (j : Fin 2) (w : List Bool) : Bool :=
  MultiTapeTM.indicator (dropBank j : Set (List Bool)) w

/-- The common bounded guard uses exactly the brief's linear register bound. -/
private abbrev DropGood (mode : Bool) (h : List Bool) (a : AConf 9 DropState) :=
  PreS (dropARM mode) h a ∧ ∀ r, a.2.1 r ≤ 4 * h.length + 4

/-- Bounded reachability is the received relation, with the fixed table and oracle. -/
private abbrev DropReach (mode : Bool) (h : List Bool) :=
  AReach (dropARM mode) dropOracle h (DropGood mode h)

/-- Halting uses the same received relation and guard. -/
private abbrev DropHalt (mode : Bool) (h : List Bool) :=
  AHalt (dropARM mode) dropOracle h (DropGood mode h)

/-- A register vector for the phase boundaries of the index-dropping machine. -/
private def dropValues (n : ℕ) (ptr zend retained inner kept query temp tail : ℕ := 0) : Fin 9 → ℕ :=
  ![ptr, n, zend, retained, inner, kept, query, temp, tail]

/-- A bit call reads the corresponding host position, including its false default. -/
private lemma drop_bit (h : List Bool) (i : ℕ) :
    dropOracle 0 (pairEncode h (Nat.bits i)) = h.getD i false := by
  change MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _
  exact indicator_inputBitLang h i

/-- A length call tests a host position. -/
private lemma drop_len (h : List Bool) (i : ℕ) :
    dropOracle 1 (pairEncode h (Nat.bits i)) = decide (i < h.length) := by
  change MultiTapeTM.indicator (inputLenLang : Set (List Bool)) _ = _
  exact indicator_inputLenLang h i

/-- Returning a bit halts in one bounded step. -/
private lemma drop_ret (mode b : Bool) (h : List Bool) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * h.length + 4) :
    DropHalt mode h (some (.answer b), v, none) b :=
  AHalt.ret rfl ⟨drop_preS mode h _, hv⟩

/-- At a matching index the length mode accepts; the bit mode calls the access bank. -/
private lemma drop_hit (mode : Bool) (h : List Bool) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * h.length + 4) :
    DropHalt mode h (some .hit, v, none) (if mode then true else h.getD (v 0) false) := by
  cases mode
  · apply AHalt.step ⟨drop_preS false h _, hv⟩
    rw [astep_call (show dropARM false .hit = _ from rfl)]
    simp only [vword_whole₁, drop_bit]
    cases hb : h.getD (v 0) false <;> simpa [hb] using drop_ret false _ h v hv
  · exact AHalt.ret rfl ⟨drop_preS true h _, hv⟩

/-- Every copy stage instantiates the one shared bounded copy loop. -/
private lemma drop_copy_run (mode : Bool) (h : List Bool) (stage : Fin 8) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * h.length + 4)
    (hle : v (dropCopy stage).1 ≤ v (dropCopy stage).2.1) :
    DropReach mode h (some (.copy stage false), v, none)
      (some (dropCopy stage).2.2,
        Function.update v (dropCopy stage).1 (v (dropCopy stage).2.1), none) := by
  exact registerCopy_loop (dropARM mode) dropOracle h _ _
    ((by decide : ∀ s, (dropCopy s).1 ≠ (dropCopy s).2.1) stage)
    _ _ _ rfl rfl _ v hv hle

/-- Every nested pair scan is an instance of the received strided pair validator. -/
private lemma drop_pair_run (mode : Bool) (h : List Bool) (layer : Fin 3)
    (w : List Bool) (v : Fin 9 → ℕ) (hv : ∀ r, v r ≤ 4 * h.length + 4)
    (hl : v (dropLimit layer) = v 0 + dropStride layer * w.length)
    (ho : ∀ i < w.length, h.getD (v 0 + dropStride layer * i) false = w.getD i false) :
    match pairDecode w with
    | none => ∃ t ≤ w.length, DropReach mode h (some (.scan layer), v, none)
        (some (.answer false), Function.update v 0 (v 0 + dropStride layer * t), none)
    | some (a, _) => DropReach mode h (some (.scan layer), v, none)
        (some (dropScanDone layer),
          Function.update v 0 (v 0 + dropStride layer * (2 * a.length + 2)), none) := by
  apply alignedPair_loop (dropARM mode) dropOracle h 0 (dropLimit layer) 0
    (.scan layer) (.first layer) (.second layer) (.readSecond layer)
    (.answer false) (dropScanDone layer) (dropAdvance layer) (dropStride layer) _
    ((by decide : ∀ l, 0 < dropStride l) layer)
    ((by decide : ∀ l, (0 : Fin 9) ≠ dropLimit l) layer) rfl rfl
    (fun _ => rfl) (fun _ => rfl)
  · intro choice i hi
    simp only [dropAdvance, dif_pos hi, dropARM]
  · simp [dropAdvance]
  · exact hv
  · exact hl
  · intro i hi
    rw [drop_bit]
    exact ho i hi

/-- Lookup exposes a phase-boundary vector only when its register is supplied. -/
@[simp] private lemma dropValues_apply (n p z s u f q t a : ℕ) (r : Fin 9) :
    dropValues n p z s u f q t a r = ![p, n, z, s, u, f, q, t, a] r := rfl

/-- One register update preserves the boundary-vector representation. -/
@[simp] private lemma dropValues_update (n p z s u f q t a : ℕ) (r : Fin 9) (b : ℕ) :
    Function.update (dropValues n p z s u f q t a) r b =
      dropValues (if 1 = r then b else n) (if 0 = r then b else p)
        (if 2 = r then b else z) (if 3 = r then b else s) (if 4 = r then b else u)
        (if 5 = r then b else f) (if 6 = r then b else q) (if 7 = r then b else t)
        (if 8 = r then b else a) := by
  apply funext
  simp [Fin.forall_fin_succ, dropValues, Function.update_apply]

/-- Bounds on a boundary vector are the nine scalar bounds. -/
private lemma dropValues_bound (n p z s u f q t a B : ℕ)
    (hn : n ≤ B) (hp : p ≤ B) (hz : z ≤ B) (hs : s ≤ B) (hu : u ≤ B)
    (hf : f ≤ B) (hq : q ≤ B) (ht : t ≤ B) (ha : a ≤ B) :
    ∀ r, dropValues n p z s u f q t a r ≤ B := by
  simpa [Fin.forall_fin_succ] using ⟨hp, hn, hz, hs, hu, hf, hq, ht, ha⟩

/-- Successful outer validation decodes the bounded query; either failed test rejects.
The proof uses the shared tail scanner before the shared reverse decoder.

**Proof sketch.** Save the tail start and copy the host length into the width cap. The tail
scan either rejects or establishes canonicality and the width bound. Clear its scratch,
restore the pointer to the host end, and invoke bounded decoding. Its accumulator bounds
come from the frozen suffix-value lemma. No arbitrary payload is decoded numerically. -/
private lemma drop_tail_decode (mode : Bool) (z tail : List Bool) :
    let h := pairEncode z tail
    let p := 2 * z.length + 2
    if Canon tail ∧ tail.length ≤ (Nat.bits h.length).length then
      DropReach mode h
        (some (.copy 0 false), dropValues h.length (ptr := p), none)
        (some (.copy 3 false), dropValues h.length (ptr := p) (query := bitsVal tail) (tail := p), none)
    else DropHalt mode h
      (some (.copy 0 false), dropValues h.length (ptr := p), none) false := by
  dsimp only
  let h := pairEncode z tail
  let p := 2 * z.length + 2
  have len : h.length = p + tail.length := length_pairEncode z tail
  have pn : p ≤ h.length := by omega
  let v₀ := dropValues h.length (ptr := p)
  let v₁ := dropValues h.length (ptr := p) (tail := p)
  let v₂ := dropValues h.length (ptr := p) (temp := h.length) (tail := p)
  have bounds : ∀ (ptr temp : ℕ), ptr ≤ h.length → temp ≤ h.length →
      ∀ r, (dropValues h.length (ptr := ptr) (temp := temp) (tail := p)) r ≤ 4 * h.length + 4 := by
    intro ptr temp hp ht
    apply dropValues_bound <;> omega
  have b₀ : ∀ r, v₀ r ≤ 4 * h.length + 4 := by
    dsimp [v₀]; apply dropValues_bound <;> omega
  have b₁ := bounds p 0 pn (Nat.zero_le _)
  have b₂ := bounds p h.length pn le_rfl
  have c₀ : DropReach mode h (some (.copy 0 false), v₀, none)
      (some (.copy 1 false), v₁, none) := by
    simpa [v₀, v₁, dropCopy] using drop_copy_run mode h 0 v₀ b₀ (by simp [v₀, dropCopy])
  have c₁ : DropReach mode h (some (.copy 1 false), v₁, none)
      (some (.tailTest true), v₂, none) := by
    simpa [v₁, v₂, dropCopy] using drop_copy_run mode h 1 v₁ b₁ (by simp [v₁, dropCopy])
  have reads : ∀ i < tail.length,
      dropOracle 0 (pairEncode h (Nat.bits (v₂ 0 + 1 * i))) = tail.getD i false := by
    intro i hi
    rw [drop_bit]
    simp only [v₂, dropValues_apply, Matrix.cons_val_zero, one_mul]
    rw [show p + i = 2 * z.length + 2 + i by rfl]
    rw [show h = pairEncode z tail by rfl, pairEncode_getD]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    congr 1
    omega
  obtain ⟨v, bv, vp, frame, scan⟩ := canonicalTail_loop (dropARM mode) dropOracle h
    0 1 7 (by decide) (by decide) (by decide) 0 DropState.tailTest
    .tailCheck .tailRead (.answer false) .tailDone DropState.tailHalf dropTailAdvance 1
    (4 * h.length + 4) (by omega) (fun _ => rfl) rfl rfl
    (fun _ => rfl)
    (by
      intro b i hi
      have hi0 : i = 0 := by omega
      subst i
      rfl)
    (fun _ => rfl) tail true v₂ b₂
    (by simpa [v₂] using len) reads
  have fn : v 1 = h.length := by simpa [v₂] using frame 1 (by decide) (by decide)
  have ft : v 8 = p := by simpa [v₂] using frame 8 (by decide) (by decide)
  by_cases good : Canon tail ∧ tail.length ≤ (Nat.bits h.length).length
  · rw [if_pos good]
    have flag := (drop_canon tail).mpr good.1
    have scan' : DropReach mode h (some (.tailTest true), v₂, none) (some .tailDone, v, none) := by
      have ss := scan
      simp only [flag, ↓reduceIte] at ss
      simpa [v₂, good.2] using ss
    have reset : DropReach mode h (some .tailDone, v, none)
        (some (.copy 2 false), dropValues h.length (tail := p), none) := by
      apply AReach.step ⟨drop_preS mode h _, bv⟩
      simp only [astep_clr (show dropARM mode .tailDone = _ from rfl)]
      apply AReach.step ⟨drop_preS mode h _, register_update_le v 7 _ 0 bv (by omega)⟩
      simp only [astep_clr (show dropARM mode (.clearPtr 0) = _ from rfl)]
      have ve : Function.update (Function.update v 7 0) 0 0 = dropValues h.length (tail := p) := by
        apply funext
        have fr := frame
        simp only [Fin.forall_fin_succ] at fr ⊢
        simp_all [v₂, Function.update_apply]
      rw [ve]
      exact AReach.refl _
    let vd := dropValues h.length (ptr := h.length) (tail := p)
    have bd : ∀ r, vd r ≤ 4 * h.length + 4 := bounds h.length 0 le_rfl (Nat.zero_le _)
    have cp : DropReach mode h (some (.copy 2 false), dropValues h.length (tail := p), none)
        (some .decode, vd, none) := by
      simpa [vd, dropCopy] using drop_copy_run mode h 2 (dropValues h.length (tail := p))
        (bounds 0 0 (Nat.zero_le _) (Nat.zero_le _)) (by simp [dropCopy])
    have vals : ∀ i ≤ tail.length, bitsVal (tail.drop i) ≤ 4 * h.length + 4 := by
      intro i _
      have := query_accumulator_bound tail h.length i good.1 good.2
      omega
    have dread : ∀ i < tail.length,
        dropOracle 0 (pairEncode h (Nat.bits (vd 8 + i))) = tail.getD i false := by
      simpa only [vd, v₂, dropValues_apply, Matrix.cons_val_succ, Matrix.cons_val_zero,
        Nat.one_mul] using reads
    obtain ⟨vf, bf, ep, ea, et, ef, dec⟩ := boundedDecode_loop (dropARM mode) dropOracle h
      0 8 6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      0 .decode .decodeDown .decodeRead (.copy 3 false)
      DropState.decodeCopy DropState.decodeCopyInc DropState.decodeClear
      DropState.decodeScale DropState.decodeTake DropState.decodeAdd dropDecodeAdvance
      rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)
      (by
        intro b i hi
        have hi01 : i = 0 ∨ i = 1 := by omega
        rcases hi01 with rfl | rfl <;> rfl)
      (fun _ => rfl) (fun _ => rfl) tail (4 * h.length + 4) vals tail.length le_rfl vd bd
      (by simpa [vd] using len) (by simp [vd, bitsVal]) (by simp [vd]) dread
    have endpoint : vf = dropValues h.length (ptr := p) (query := bitsVal tail) (tail := p) := by
      apply funext
      simp only [Fin.forall_fin_succ] at ef ⊢
      simp_all [vd]
    rw [endpoint] at dec
    exact (c₀.trans c₁).trans (scan'.trans (reset.trans (cp.trans dec)))
  · rw [if_neg good]
    have stop : DropReach mode h (some (.tailTest true), v₂, none)
        (some (.answer false), v, none) := by
      by_cases width : tail.length ≤ (Nat.bits h.length).length
      · have nc : ¬ Canon tail := fun hc => good ⟨hc, width⟩
        have flag : tail.getLastD true = false := Bool.eq_false_iff.mpr (fun ht => nc ((drop_canon tail).mp ht))
        have ss := scan
        simp only [flag, Bool.false_eq_true, ↓reduceIte, ite_self] at ss
        exact ss
      · simpa [v₂, width] using scan
    exact ((c₀.trans c₁).trans stop).halt (drop_ret mode false h v bv)

/-- Both lookup segments instantiate the same bounded indexing fragment. -/
private lemma drop_seek_run (mode suffix : Bool) (h : List Bool) (count : ℕ) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * h.length + 4)
    (hl : v (if suffix then 2 else 5) = v 0 + (if suffix then 2 else 4) * count)
    (hb : v 7 + count ≤ 4 * h.length + 4) (hq : v 7 ≤ v 6) :
    if v 6 < v 7 + count then
      DropReach mode h (some (.seek suffix), v, none)
        (some .hit, Function.update (Function.update v 0
          (v 0 + (if suffix then 2 else 4) * (v 6 - v 7))) 7 (v 6), none)
    else
      DropReach mode h (some (.seek suffix), v, none)
        (some (if suffix then .answer false else .clearPtr 4),
          Function.update (Function.update v 0 (v (if suffix then 2 else 5))) 7 (v 7 + count), none) := by
  apply indexedSeek_loop (dropARM mode) dropOracle h 0 (if suffix then 2 else 5) 7 6
    (by cases suffix <;> decide) (by decide) (by decide)
    (by cases suffix <;> decide) (by cases suffix <;> decide) (by decide)
    (.seek suffix) (.matchIndex suffix) (.nextIndex suffix) .hit
    (if suffix then .answer false else .clearPtr 4) (dropWalk suffix)
    (if suffix then 2 else 4) _ (by cases suffix <;> decide) rfl rfl rfl
  · intro i hi
    simp only [dropWalk, dif_pos hi, dropARM]
  · simp [dropWalk]
  · exact hv
  · exact hl
  · exact hb
  · exact hq

/-- The final lookup reads the kept prefix at stride four, then the retained suffix at
stride two. The discarded and retained fields have no canonicality hypothesis.

**Proof sketch.** The shared bounded seek either hits inside the kept prefix or reaches
its end. On a miss, relocate the pointer to the retained suffix and use the same seek
again. The frozen prefix/suffix address lemmas identify each hit with the output bit;
the end-of-suffix branch is precisely an out-of-range query. -/
private lemma drop_lookup (mode : Bool) (w b b' : List Bool) (q : ℕ) (v : Fin 9 → ℕ)
    (hv : ∀ r, v r ≤ 4 * (pairEncode (pairEncode (pairEncode w b) b') (Nat.bits q)).length + 4)
    (hp : v 0 = 0) (hk : v 5 = 4 * (2 * w.length + 2))
    (hs : v 3 = 4 * (pairEncode w b).length + 4)
    (he : v 2 = 4 * (pairEncode w b).length + 4 + 2 * b'.length)
    (hq : v 6 = q) (hi : v 7 = 0) :
    DropHalt mode (pairEncode (pairEncode (pairEncode w b) b') (Nat.bits q))
      (some (.seek false), v, none)
      (if mode then decide (q < (dropIdx (pairEncode (pairEncode w b) b')).length)
        else (dropIdx (pairEncode (pairEncode w b) b')).getD q false) := by
  let h := pairEncode (pairEncode (pairEncode w b) b') (Nat.bits q)
  change ∀ r, v r ≤ 4 * h.length + 4 at hv
  let n := 2 * w.length + 2
  let out := dropIdx (pairEncode (pairEncode w b) b')
  have outlen : out.length = n + b'.length := by simp [out, n, dropIdx_pairEncode, length_pairEncode]
  have nb : n ≤ 4 * h.length + 4 := by have := hv 5; change v 5 = 4 * n at hk; omega
  have total : n + b'.length ≤ 4 * h.length + 4 := by simp only [h, n, length_pairEncode]; omega
  have first := drop_seek_run mode false h n v hv (by simpa [hp, n] using hk)
    (by simpa [hi] using nb) (by simp [hi])
  by_cases lt : q < n
  · have cond : v 6 < v 7 + n := by omega
    simp only [if_pos cond, Bool.false_eq_true, ↓reduceIte] at first
    let vh := Function.update (Function.update v 0 (4 * q)) 7 q
    have run : DropReach mode h (some (.seek false), v, none) (some .hit, vh, none) := by
      simpa [hp, hq, hi, vh] using first
    have pos : 4 * q ≤ 4 * h.length + 4 := by have := hv 5; change v 5 = 4 * n at hk; omega
    have bv : ∀ r, vh r ≤ 4 * h.length + 4 := register_update_le _ 7 _ q
      (register_update_le v 0 _ _ hv pos) (by simpa [hq] using hv 6)
    have bit := dropIdx_prefix_address w b b' (Nat.bits q) q lt
    have ans : (if mode then true else h.getD (vh 0) false) =
        (if mode then decide (q < out.length) else out.getD q false) := by
      have inside : q < out.length := by omega
      cases mode with
      | false =>
        change h.getD (4 * q) false = out.getD q false
        exact bit.symm
      | true => simp [inside]
    rw [← ans]
    exact run.halt (drop_hit mode h vh bv)
  · have cond : ¬ v 6 < v 7 + n := by omega
    simp only [if_neg cond, Bool.false_eq_true, ↓reduceIte] at first
    let vm := Function.update (Function.update v 0 (v 5)) 7 n
    have run : DropReach mode h (some (.seek false), v, none) (some (.clearPtr 4), vm, none) := by
      simpa [hi, vm] using first
    have bm : ∀ r, vm r ≤ 4 * h.length + 4 := register_update_le _ 7 _ n
      (register_update_le v 0 _ _ hv (hv 5)) nb
    let vs := Function.update vm 0 (v 3)
    have bs : ∀ r, vs r ≤ 4 * h.length + 4 := register_update_le vm 0 _ _ bm (hv 3)
    have move : DropReach mode h (some (.clearPtr 4), vm, none) (some (.seek true), vs, none) := by
      apply AReach.step ⟨drop_preS mode h _, bm⟩
      simp only [astep_clr (show dropARM mode (.clearPtr 4) = _ from rfl)]
      have copy := drop_copy_run mode h 7 (Function.update vm 0 0)
        (register_update_le vm 0 _ 0 bm (by omega)) (by simp [dropCopy])
      simpa [dropCopy, vs, vm] using copy
    have vp : vs 0 = 4 * (pairEncode w b).length + 4 := by simp [vs, hs]
    have ve : vs 2 = 4 * (pairEncode w b).length + 4 + 2 * b'.length := by simp [vs, vm, he]
    have vi : vs 7 = n := by simp [vs, vm]
    have vq : vs 6 = q := by simp [vs, vm, hq]
    have second := drop_seek_run mode true h b'.length vs bs
      (by simpa [vp] using ve) (by simpa [vi] using total) (by rw [vi, vq]; omega)
    by_cases inrange : q < n + b'.length
    · have cond' : vs 6 < vs 7 + b'.length := by omega
      simp only [if_pos cond', ↓reduceIte] at second
      let addr := 4 * (pairEncode w b).length + 4 + 2 * (q - n)
      let vh := Function.update (Function.update vs 0 addr) 7 q
      have hit : DropReach mode h (some (.seek true), vs, none) (some .hit, vh, none) := by
        simpa [vp, vq, vi, addr, vh] using second
      have pos : addr ≤ 4 * h.length + 4 := by have := hv 2; dsimp [addr]; omega
      have bh : ∀ r, vh r ≤ 4 * h.length + 4 := register_update_le _ 7 _ q
        (register_update_le vs 0 _ _ bs pos) (by simpa [hq] using hv 6)
      have jlt : q - n < b'.length := by omega
      have bit := dropIdx_suffix_address w b b' (Nat.bits q) (q - n) jlt
      have qeq : 2 * w.length + 2 + (q - n) = q := by dsimp [n] at *; omega
      rw [qeq] at bit
      have ans : (if mode then true else h.getD (vh 0) false) =
          (if mode then decide (q < out.length) else out.getD q false) := by
        have inside : q < out.length := by omega
        cases mode with
        | false =>
          change h.getD addr false = out.getD q false
          exact bit.symm
        | true => simp [inside]
      rw [← ans]
      exact (run.trans (move.trans hit)).halt (drop_hit mode h vh bh)
    · have cond' : ¬ vs 6 < vs 7 + b'.length := by omega
      simp only [if_neg cond', ↓reduceIte] at second
      let vf := Function.update (Function.update vs 0 (vs 2)) 7 (vs 7 + b'.length)
      have bf : ∀ r, vf r ≤ 4 * h.length + 4 := register_update_le _ 7 _ _
        (register_update_le vs 0 _ _ bs (bs 2)) (by rw [vi]; exact total)
      have bit : out.getD q false = false := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show out.length ≤ q by omega)]
      have ans : (if mode then decide (q < out.length) else out.getD q false) = false := by
        cases mode with
        | false => exact bit
        | true => simp [show ¬ q < out.length by omega]
      rw [ans]
      exact (run.trans (move.trans second)).halt (drop_ret mode false h vf bf)

/-- Reading an even position in a paired first field removes one doubling. -/
private lemma drop_first_read (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (pairEncode a b).getD (2 * i) false = a.getD i false := by
  rw [pairEncode_getD, if_pos (by omega)]
  congr 1
  omega

/-- A finite subtraction chain preserves the common register bound. The two nested-pair
preparations use this same argument for their physical separator widths. -/
private lemma drop_decrement_run (mode : Bool) (h : List Bool) (r : Fin 9) (count : ℕ)
    (path : ℕ → DropState) (v : Fin 9 → ℕ) (hv : ∀ j, v j ≤ 4 * h.length + 4)
    (steps : ∀ i < count, dropARM mode (path i) = .dec r (path (i + 1))) :
    DropReach mode h (some (path 0), v, none)
      (some (path count), Function.update v r (v r - count), none) := by
  induction count generalizing path v with
  | zero => simpa using AReach.refl (some (path 0), v, none)
  | succ count ih =>
    apply AReach.step ⟨drop_preS mode h _, hv⟩
    simp only [astep_dec (steps 0 (by omega))]
    have bound := register_update_le v r (4 * h.length + 4) (v r - 1) hv
      (by have := hv r; omega)
    have rest := ih (fun i => path (i + 1)) (Function.update v r (v r - 1)) bound
      (fun i hi => steps (i + 1) (by omega))
    simpa [Function.update_idem, Nat.sub_sub, Nat.add_comm] using rest

/-- After decoding the query, prepare the physical end of its first field and restart its
pair-shape scan. This stores no payload value.

**Proof sketch.** Copy the saved tail start, subtract the two separator cells, and clear
only the physical pointer before entering the received scan. -/
private lemma drop_z_prepare (mode : Bool) (h : List Bool) (zlen q : ℕ)
    (hz : 2 * zlen + 2 ≤ h.length) (hq : q ≤ 2 * h.length) :
    DropReach mode h
      (some (.copy 3 false), dropValues h.length (ptr := 2 * zlen + 2)
        (query := q) (tail := 2 * zlen + 2), none)
      (some (.scan 1), dropValues h.length (zend := 2 * zlen)
        (query := q) (tail := 2 * zlen + 2), none) := by
  have bv : ∀ r, (dropValues h.length (ptr := 2 * zlen + 2)
      (query := q) (tail := 2 * zlen + 2)) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have cp := drop_copy_run mode h 3 _ bv (by simp [dropCopy])
  simp [dropCopy] at cp
  apply cp.trans
  have dec := drop_decrement_run mode h 2 2
    (fun i => if i = 0 then .zDec 0 else if i = 1 then .zDec 1 else .clearPtr 1)
    (dropValues h.length (ptr := 2 * zlen + 2) (zend := 2 * zlen + 2)
      (query := q) (tail := 2 * zlen + 2))
    (by apply dropValues_bound <;> omega)
    (by intro i hi; have : i = 0 ∨ i = 1 := by omega
        rcases this with rfl | rfl <;> rfl)
  simp at dec
  apply dec.trans
  apply AReach.step ⟨drop_preS mode h _, by apply dropValues_bound <;> omega⟩
  simp [astep_clr (show dropARM mode (.clearPtr 1) = _ from rfl)]
  exact AReach.refl _

/-- Save the retained suffix start, derive the inner first-field end, and restart the
stride-four pair scan. Both offsets remain in host coordinates.

**Proof sketch.** Copy the separator end into the retained-start and inner-end registers,
subtract its four physical separator cells from the latter, and clear the pointer. -/
private lemma drop_u_prepare (mode : Bool) (h : List Bool) (zlen ulen q : ℕ)
    (hz : 2 * zlen + 2 ≤ h.length) (hu : 2 * ulen + 2 ≤ zlen) (hq : q ≤ 2 * h.length) :
    DropReach mode h
      (some (.copy 4 false), dropValues h.length (ptr := 4 * ulen + 4) (zend := 2 * zlen)
        (query := q) (tail := 2 * zlen + 2), none)
      (some (.scan 2), dropValues h.length (zend := 2 * zlen) (retained := 4 * ulen + 4)
        (inner := 4 * ulen) (query := q) (tail := 2 * zlen + 2), none) := by
  have bv : ∀ r, (dropValues h.length (ptr := 4 * ulen + 4) (zend := 2 * zlen)
      (query := q) (tail := 2 * zlen + 2)) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have c₄ := drop_copy_run mode h 4 _ bv (by simp [dropCopy])
  simp [dropCopy] at c₄
  apply c₄.trans
  have bv' : ∀ r, (dropValues h.length (ptr := 4 * ulen + 4) (zend := 2 * zlen)
      (retained := 4 * ulen + 4) (query := q) (tail := 2 * zlen + 2)) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have c₅ := drop_copy_run mode h 5 _ bv' (by simp [dropCopy])
  simp [dropCopy] at c₅
  apply c₅.trans
  have dec := drop_decrement_run mode h 4 4
    (fun i => if hi : i < 4 then .uDec ⟨i, hi⟩ else .clearPtr 2)
    (dropValues h.length (ptr := 4 * ulen + 4) (zend := 2 * zlen)
      (retained := 4 * ulen + 4) (inner := 4 * ulen + 4)
      (query := q) (tail := 2 * zlen + 2))
    (by apply dropValues_bound <;> omega)
    (by intro i hi; have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> rfl)
  simp at dec
  apply dec.trans
  apply AReach.step ⟨drop_preS mode h _, by apply dropValues_bound <;> omega⟩
  simp [astep_clr (show dropARM mode (.clearPtr 2) = _ from rfl)]
  exact AReach.refl _

/-- Save the last pair boundary and restart the final segmented lookup. -/
private lemma drop_lookup_prepare (mode : Bool) (h : List Bool) (zlen ulen wlen q : ℕ)
    (hz : 2 * zlen + 2 ≤ h.length) (hu : 2 * ulen + 2 ≤ zlen)
    (hw : 2 * wlen + 2 ≤ ulen) (hq : q ≤ 2 * h.length) :
    DropReach mode h
      (some (.copy 6 false), dropValues h.length (ptr := 8 * wlen + 8) (zend := 2 * zlen)
        (retained := 4 * ulen + 4) (inner := 4 * ulen) (query := q) (tail := 2 * zlen + 2), none)
      (some (.seek false), dropValues h.length (zend := 2 * zlen) (retained := 4 * ulen + 4)
        (inner := 4 * ulen) (kept := 8 * wlen + 8) (query := q) (tail := 2 * zlen + 2), none) := by
  have bv : ∀ r, (dropValues h.length (ptr := 8 * wlen + 8) (zend := 2 * zlen)
      (retained := 4 * ulen + 4) (inner := 4 * ulen) (query := q)
      (tail := 2 * zlen + 2)) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have cp := drop_copy_run mode h 6 _ bv (by simp [dropCopy])
  simp [dropCopy] at cp
  apply cp.trans
  apply AReach.step ⟨drop_preS mode h _, by apply dropValues_bound <;> omega⟩
  simp [astep_clr (show dropARM mode (.clearPtr 3) = _ from rfl)]
  exact AReach.refl _

/-- Scan the inner pair after the outer payload pair has been recognized.

**Proof sketch.** Derive the inner end from the saved separator address, then instantiate
the received stride-four scan. A failed decode gives an empty output. A successful decode
saves the final prefix boundary and enters the proved segmented lookup. -/
private lemma drop_inner_run (mode : Bool) (u b' : List Bool) (q : ℕ)
    (hq : q ≤ 2 * (pairEncode (pairEncode u b') (Nat.bits q)).length) :
    let h := pairEncode (pairEncode u b') (Nat.bits q)
    let zlen := (pairEncode u b').length
    DropHalt mode h
      (some (.copy 4 false), dropValues h.length (ptr := 4 * u.length + 4) (zend := 2 * zlen)
        (query := q) (tail := 2 * zlen + 2), none)
      (if mode then decide (q < (dropIdx (pairEncode u b')).length)
        else (dropIdx (pairEncode u b')).getD q false) := by
  dsimp only
  let h := pairEncode (pairEncode u b') (Nat.bits q)
  let zlen := (pairEncode u b').length
  change q ≤ 2 * h.length at hq
  have hz : 2 * zlen + 2 ≤ h.length := by simp [h, zlen, length_pairEncode]
  have hu : 2 * u.length + 2 ≤ zlen := by simp [zlen, length_pairEncode]
  let v := dropValues h.length (zend := 2 * zlen) (retained := 4 * u.length + 4)
    (inner := 4 * u.length) (query := q) (tail := 2 * zlen + 2)
  have bv : ∀ r, v r ≤ 4 * h.length + 4 := by dsimp [v]; apply dropValues_bound <;> omega
  have prep := drop_u_prepare mode h zlen u.length q hz hu hq
  have reads : ∀ i < u.length, h.getD (v 0 + dropStride 2 * i) false = u.getD i false := by
    intro i hi
    have outer := drop_first_read (pairEncode u b') (Nat.bits q) (2 * i)
      (by rw [length_pairEncode]; omega)
    have inner := drop_first_read u b' i hi
    simpa [v, dropStride, h, show 2 * (2 * i) = 4 * i by omega] using outer.trans inner
  have scan := drop_pair_run mode h 2 u v bv (by simp [v, dropLimit, dropStride]) reads
  cases dec : pairDecode u with
  | none =>
    simp only [dec] at scan
    obtain ⟨t, ht, run⟩ := scan
    have bp : v 0 + dropStride 2 * t ≤ 4 * h.length + 4 := by simp only [v, dropValues_apply]; simp [dropStride]; omega
    have br := register_update_le v 0 _ _ bv bp
    have ans : (if mode then decide (q < (dropIdx (pairEncode u b')).length)
        else (dropIdx (pairEncode u b')).getD q false) = false := by
      simp [dropIdx, pairDecode_pairEncode, dec]
    rw [ans]
    exact (prep.trans run).halt (drop_ret mode false h _ br)
  | some pair =>
    rcases pair with ⟨w, b⟩
    have ue := eq_pairEncode_of_pairDecode u w b dec
    subst u
    have hw : 2 * w.length + 2 ≤ (pairEncode w b).length := by simp [length_pairEncode]
    simp only [pairDecode_pairEncode] at scan
    have scan' : DropReach mode h (some (.scan 2), v, none)
        (some (.copy 6 false), dropValues h.length (ptr := 8 * w.length + 8) (zend := 2 * zlen)
          (retained := 4 * (pairEncode w b).length + 4) (inner := 4 * (pairEncode w b).length)
          (query := q) (tail := 2 * zlen + 2), none) := by
      simpa [v, dropStride, dropScanDone, show 4 * (2 * w.length + 2) = 8 * w.length + 8 by omega] using scan
    have last := drop_lookup_prepare mode h zlen (pairEncode w b).length w.length q hz hu hw hq
    let vf := dropValues h.length (zend := 2 * zlen) (retained := 4 * (pairEncode w b).length + 4)
      (inner := 4 * (pairEncode w b).length) (kept := 8 * w.length + 8)
      (query := q) (tail := 2 * zlen + 2)
    have bf : ∀ r, vf r ≤ 4 * h.length + 4 := by dsimp [vf]; apply dropValues_bound <;> omega
    have lookup := drop_lookup mode w b b' q vf bf (by simp [vf])
      (by simp [vf]; omega) (by simp [vf]) (by simp [vf, zlen, length_pairEncode]; omega)
      (by simp [vf]) (by simp [vf])
    exact (prep.trans (scan'.trans last)).halt lookup

/-- Scan the outer payload pair after the bounded query value is available.

**Proof sketch.** Prepare the physical first-field end and cite the received stride-two
pair scan. Malformed payloads have empty output. Otherwise the scan's boundary is precisely
the retained suffix start, and the inner-pair run completes the computation. -/
private lemma drop_nested_run (mode : Bool) (z : List Bool) (q : ℕ)
    (hq : q ≤ 2 * (pairEncode z (Nat.bits q)).length) :
    let h := pairEncode z (Nat.bits q)
    DropHalt mode h
      (some (.copy 3 false), dropValues h.length (ptr := 2 * z.length + 2)
        (query := q) (tail := 2 * z.length + 2), none)
      (if mode then decide (q < (dropIdx z).length) else (dropIdx z).getD q false) := by
  dsimp only
  let h := pairEncode z (Nat.bits q)
  change q ≤ 2 * h.length at hq
  have hz : 2 * z.length + 2 ≤ h.length := by simp [h, length_pairEncode]
  let v := dropValues h.length (zend := 2 * z.length) (query := q) (tail := 2 * z.length + 2)
  have bv : ∀ r, v r ≤ 4 * h.length + 4 := by dsimp [v]; apply dropValues_bound <;> omega
  have prep := drop_z_prepare mode h z.length q hz hq
  have scan := drop_pair_run mode h 1 z v bv (by simp [v, dropLimit, dropStride])
    (by intro i hi; simpa [v, dropStride, h] using drop_first_read z (Nat.bits q) i hi)
  cases dec : pairDecode z with
  | none =>
    simp only [dec] at scan
    obtain ⟨t, ht, run⟩ := scan
    have bp : v 0 + dropStride 1 * t ≤ 4 * h.length + 4 := by simp [v, dropStride]; omega
    have br := register_update_le v 0 _ _ bv bp
    have ans : (if mode then decide (q < (dropIdx z).length) else (dropIdx z).getD q false) = false := by
      simp [dropIdx, dec]
    rw [ans]
    exact (prep.trans run).halt (drop_ret mode false h _ br)
  | some pair =>
    rcases pair with ⟨u, b'⟩
    have ze := eq_pairEncode_of_pairDecode z u b' dec
    subst z
    simp only [pairDecode_pairEncode] at scan
    have scan' : DropReach mode h (some (.scan 1), v, none)
        (some (.copy 4 false), dropValues h.length (ptr := 4 * u.length + 4)
          (zend := 2 * (pairEncode u b').length) (query := q)
          (tail := 2 * (pairEncode u b').length + 2), none) := by
      simpa [v, dropStride, dropScanDone, show 2 * (2 * u.length + 2) = 4 * u.length + 4 by omega] using scan
    exact (prep.trans scan').halt (drop_inner_run mode u b' q hq)

/-- The mode-parametrized language has the intended answer on every canonical query. -/
private lemma drop_lang_pair (mode : Bool) (z : List Bool) (q : ℕ) :
    MultiTapeTM.indicator (dropLang mode : Set (List Bool)) (pairEncode z (Nat.bits q)) =
      (if mode then decide (q < (dropIdx z).length) else (dropIdx z).getD q false) := by
  cases mode <;> simp [dropLang, indicator_indexLang_pairEncode]

/-- A failed outer pair decode excludes membership in either query language. -/
private lemma drop_bad_shape (mode : Bool) (h : List Bool) (hh : pairDecode h = none) :
    MultiTapeTM.indicator (dropLang mode : Set (List Bool)) h = false := by
  have no : h ∉ dropLang mode := by
    rintro ⟨z, q, rfl, _⟩
    simp [pairDecode_pairEncode] at hh
  simp [MultiTapeTM.indicator, no]

/-- A noncanonical index tail excludes membership in either query language. -/
private lemma drop_bad_tail (mode : Bool) (z tail : List Bool) (hc : ¬ Canon tail) :
    MultiTapeTM.indicator (dropLang mode : Set (List Bool)) (pairEncode z tail) = false := by
  have no : pairEncode z tail ∉ dropLang mode := by
    rintro ⟨w, q, eq, _⟩
    have fields := pairEncode_injective (a₁ := (z, tail)) (a₂ := (w, Nat.bits q)) eq
    have ht : tail = Nat.bits q := congrArg Prod.snd fields
    exact hc (ht ▸ canon_bits q)
  simp [MultiTapeTM.indicator, no]

/-- Rejection by canonicality or by the pre-decode width check is semantically correct. -/
private lemma drop_rejected_tail (mode : Bool) (z tail : List Bool)
    (bad : ¬ (Canon tail ∧ tail.length ≤ (Nat.bits (pairEncode z tail).length).length)) :
    MultiTapeTM.indicator (dropLang mode : Set (List Bool)) (pairEncode z tail) = false := by
  by_cases hc : Canon tail
  · obtain ⟨q, rfl⟩ : ∃ q, tail = Nat.bits q := ⟨bitsVal tail, canon_eq_bits tail hc⟩
    have width : (Nat.bits (pairEncode z (Nat.bits q)).length).length < (Nat.bits q).length := by
      have notle : ¬ (Nat.bits q).length ≤ (Nat.bits (pairEncode z (Nat.bits q)).length).length :=
        fun hw => bad ⟨hc, hw⟩
      omega
    obtain ⟨bit, len⟩ := dropIdx_query_overflow z q width
    rw [drop_lang_pair]
    cases mode with
    | false => exact bit
    | true => simp [len]
  · exact drop_bad_tail mode z tail hc

/-- The single table decides both index-dropping query languages on all host strings.

**Proof sketch.** Count the host length and validate the outer aligned pair. A malformed
host rejects. On a pair, the canonical-width validator either rejects correctly or supplies
a bounded index to the reverse decoder. The two nested shape scans and segmented lookup
then produce the query answer. Every composed segment has the same linear register bound. -/
private lemma drop_run (mode : Bool) (h : List Bool) :
    DropHalt mode h (some .lengthTest, fun _ => 0, none)
      (MultiTapeTM.indicator (dropLang mode : Set (List Bool)) h) := by
  have count := inputLength_loop (dropARM mode) dropOracle h 1 1 .lengthTest .lengthInc (.scan 0)
    rfl rfl (fun i _ => drop_len h i) (4 * h.length + 4) (by omega) (fun _ => 0)
    (by intro r; exact Nat.zero_le _) (by exact Nat.zero_le _)
  have vec : Function.update (fun _ : Fin 9 => 0) 1 h.length = dropValues h.length := by
    apply funext
    simp [Fin.forall_fin_succ, Function.update_apply]
  rw [vec] at count
  have bv : ∀ r, (dropValues h.length) r ≤ 4 * h.length + 4 := by
    apply dropValues_bound <;> omega
  have scan := drop_pair_run mode h 0 h (dropValues h.length) bv
    (by simp [dropLimit, dropStride]) (by intro i _; simp [dropStride])
  cases hd : pairDecode h with
  | none =>
    simp only [hd] at scan
    obtain ⟨t, ht, path⟩ := scan
    have bp : (dropValues h.length) 0 + dropStride 0 * t ≤ 4 * h.length + 4 := by
      simp [dropStride]; omega
    have br := register_update_le (dropValues h.length) 0 _ _ bv bp
    rw [drop_bad_shape mode h hd]
    exact (count.trans path).halt (drop_ret mode false h _ br)
  | some pair =>
    rcases pair with ⟨z, tail⟩
    have eq := eq_pairEncode_of_pairDecode h z tail hd
    subst h
    simp only [pairDecode_pairEncode] at scan
    have start : DropReach mode (pairEncode z tail) (some .lengthTest, fun _ => 0, none)
        (some (.copy 0 false), dropValues (pairEncode z tail).length (ptr := 2 * z.length + 2), none) := by
      apply count.trans
      simpa [dropStride, dropScanDone] using scan
    have decode := drop_tail_decode mode z tail
    by_cases good : Canon tail ∧ tail.length ≤ (Nat.bits (pairEncode z tail).length).length
    · simp only [if_pos good] at decode
      obtain ⟨q, rfl⟩ : ∃ q, tail = Nat.bits q := ⟨bitsVal tail, canon_eq_bits tail good.1⟩
      have qb := query_index_bound q (pairEncode z (Nat.bits q)).length good.2
      simp only [bitsVal_bits] at decode
      rw [drop_lang_pair]
      exact (start.trans decode).halt (drop_nested_run mode z q qb)
    · simp only [if_neg good] at decode
      rw [drop_rejected_tail mode z tail good]
      exact start.halt decode

/-- Compile the one bounded table against the proved input-access bank. -/
private lemma drop_mem (mode : Bool) : dropLang mode ∈ LOGSPACE := by
  have bank : ∀ j, dropBank j ∈ LOGSPACE := by
    intro j
    have cases : j = 0 ∨ j = 1 := by omega
    rcases cases with rfl | rfl
    · exact inputBitLang_mem
    · exact inputLenLang_mem
  apply arm_decides_poly (dropARM mode) .lengthTest dropBank bank 4 1
  intro h
  exact (drop_run mode h).mono (fun a ⟨hs, hv⟩ =>
    ⟨hs, fun r => by simpa [Nat.mul_add] using hv r⟩)

/-- **Dropping the middle index is implicitly logspace computable** (phase P4.4b; proved).

**Proof sketch.**

* **Bound.** `Complexity.dropIdx_length_le`.
* **The ARM.** Both query languages come from one abstract register machine with a mode bit
  over the access bank `![inputBitLang, inputLenLang]` (`inputBitLang_mem`,
  `inputLenLang_mem`), by `LogProg.arm_decides_poly`. A `whole` call on `[r]` reads the host's
  bit at `v r` (`LogProg.vword_whole₁`, `indicator_indexLang_pairEncode`).
* **The run, on a host `h = ⟨z, bits q⟩`.**
  * Validate `h` and its canonical tail.
  * Before accumulating `q`, compare the tail's length with `|bits |h||`. If longer, then
    `q ≥ |h| ≥ |dropIdx z|` and the answer is `false`.
  * Decode `z = ⟨u, b'⟩` and `u = ⟨w, b⟩` by aligned scans at strides 2 and 4 of `h`. A failed
    decode means `dropIdx z = []`, and the answer is `false`.
  * Answer by position arithmetic: positions below `2|w| + 2` come from `u`, the rest from
    `b'`.
* **Registers** are at most `4|h| + 4`. -/
theorem implicitlyLogspaceComputable_dropIdx : ImplicitlyLogspaceComputable dropIdx := by
  refine ⟨⟨1, 1, fun z => ?_⟩, ?_, ?_⟩
  · simpa using (dropIdx_length_le z).trans (Nat.le_succ z.length)
  · simpa only [dropLang, Bool.false_eq_true, ↓reduceIte] using drop_mem false
  · simpa only [dropLang, ↓reduceIte] using drop_mem true

/-! ## The composition oracle bank -/

/-- The query languages of `f` lifted through the two discarded host indices. -/
private def compLift (f : List Bool → List Bool) (lengthMode : Bool) : Language Bool :=
  {z | dropIdx (dropIdx z) ∈ indexLang (fun x i =>
    if lengthMode then i < (f x).length else (f x).getD i false = true)}

/-- Both lifted languages are in logspace by two applications of the proved preimage
construction along the now-proved index-dropping map. -/
private lemma compLift_mem {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f)
    (mode : Bool) : compLift f mode ∈ LOGSPACE := by
  have query : indexLang (fun x i => if mode then i < (f x).length
      else (f x).getD i false = true) ∈ LOGSPACE := by
    cases mode
    · exact hf.2.1
    · exact hf.2.2
  exact mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx
    (mem_LOGSPACE_preimage implicitlyLogspaceComputable_dropIdx query)

/-- The four-oracle bank for query reshaping: physical bit/length, then lifted bit/length. -/
private def compBank (f : List Bool → List Bool) : Fin 4 → Language Bool :=
  ![inputBitLang, inputLenLang, compLift f false, compLift f true]

/-- Each of the four oracle languages is proved to belong to logspace. -/
private lemma compBank_mem {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f) :
    ∀ j, compBank f j ∈ LOGSPACE := by
  intro j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj with rfl | rfl | rfl | rfl
  · exact inputBitLang_mem
  · exact inputLenLang_mem
  · exact compLift_mem hf false
  · exact compLift_mem hf true

/-- A lifted call from the twice-paired host is a genuine query about `f x`. The retained
inner payload may be arbitrary here: canonicality is a separate validation obligation. -/
private lemma compLift_query (f : List Bool → List Bool) (mode : Bool)
    (x b : List Bool) (p j : ℕ) :
    MultiTapeTM.indicator (compLift f mode : Set (List Bool))
        (pairEncode (pairEncode (pairEncode x b) (Nat.bits p)) (Nat.bits j)) =
      (if mode then decide (j < (f x).length) else (f x).getD j false) := by
  have transport : MultiTapeTM.indicator (compLift f mode : Set (List Bool))
        (pairEncode (pairEncode (pairEncode x b) (Nat.bits p)) (Nat.bits j)) =
      MultiTapeTM.indicator (indexLang (fun y i =>
        if mode then i < (f y).length else (f y).getD i false = true) : Set (List Bool))
        (pairEncode x (Nat.bits j)) := by
    simp only [compLift, MultiTapeTM.indicator, Set.mem_setOf_eq, dropIdx_pairEncode]
  rw [transport, indicator_indexLang_pairEncode]
  cases mode <;> simp

/-- The full composition output cap can be computed from the physical query-host length.
It also covers malformed inner inputs, through the landed total output-length bound. -/
private lemma compQ_host_cap {f : List Bool → List Bool} {C e : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ e) (w tail : List Bool) :
    (compQ f w).length ≤ (2 * C + 3) * ((pairEncode w tail).length + 1) ^ (e + 1) := by
  apply (compQ_length_le hf w).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp only [length_pairEncode]
  omega

/-- A canonical index wider than the full composition cap is rejected before decoding.
This uses the composition bound, rather than the shorter index-dropping bound. -/
private lemma compQ_query_overflow {f : List Bool → List Bool} {C e : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ e) (w : List Bool) (p : ℕ)
    (wide : (Nat.bits ((2 * C + 3) * ((pairEncode w (Nat.bits p)).length + 1) ^ (e + 1))).length <
      (Nat.bits p).length) :
    (compQ f w).getD p false = false ∧ ¬ p < (compQ f w).length := by
  have large : (2 * C + 3) * ((pairEncode w (Nat.bits p)).length + 1) ^ (e + 1) < p :=
    Nat.lt_of_not_ge (fun h => (Nat.not_lt_of_ge (length_bits_mono h)) wide)
  have outside : (compQ f w).length ≤ p := (compQ_host_cap hf w (Nat.bits p)).trans (Nat.le_of_lt large)
  constructor
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none outside]
  · exact Nat.not_lt.mpr outside

/-! ## B7 continuation 3: the composition-query machine -/

set_option synthInstance.maxSize 2000 in
/-- Finite control for the one composition-query ARM. The two polynomial evaluations
share their multiplication and fixed-scaling code; all input access goes through the
four proved oracle languages. -/
private inductive CompState (C e : ℕ) where
  | count | countInc
  | copy (stage : Fin 8) (bump : Bool)
  | scan (inner : Bool) | first (inner : Bool)
  | second (inner bit : Bool) | readSecond (inner bit : Bool)
  | scanInc (inner : Bool) (choice : Fin 4) (step : Fin 2)
  | outerDec (second : Bool) | baseInc
  | polyStart (outer : Bool) | power (outer : Bool) (remaining : Fin (e + 2))
  | productCopy (outer : Bool) (remaining : Fin (e + 2)) (bump : Bool)
  | productClear (outer : Bool) (remaining : Fin (e + 2))
  | productTest (outer : Bool) (remaining : Fin (e + 2))
  | productAddCopy (outer : Bool) (remaining : Fin (e + 2)) (bump : Bool)
  | productAdd (outer : Bool) (remaining : Fin (e + 2))
  | productTake (outer : Bool) (remaining : Fin (e + 2))
  | productInc (outer : Bool) (remaining : Fin (e + 2))
  | productNext (outer : Bool) (remaining : Fin (e + 2))
  | productClean (outer : Bool) (remaining : Fin (e + 2)) (second : Bool)
  | factorCopy (outer bump : Bool) | factorClear (outer : Bool)
  | factorTest (outer : Bool) | factorDown (outer : Bool)
  | factorInc (outer : Bool) (step : Fin (2 * C + 3))
  | tailTest (last : Bool) | tailCheck | tailRead | tailHalf (bit : Bool) | tailInc (bit : Bool)
  | tailDone | resetDecode
  | decode | decodeDown | decodeRead | decodeCopy (bit bump : Bool)
  | decodeClear (bit : Bool) | decodeScale (bit : Bool) | decodeTake (bit : Bool)
  | decodeInc (bit second : Bool) | decodeAdd (bit : Bool) | decodeDone
  | canonical | canonicalReset | canonicalDec (second : Bool) | canonicalRead
  | innerPrepare | innerHalf (second : Bool)
  | lengthBound | lengthQuery | lengthInc
  | doubleTest | doubleDown | doubleInc (second : Bool) | lookupReset
  | seek (suffix : Bool) | probe (suffix : Bool) | next (suffix : Bool)
  | walk (suffix second : Bool) | prefixHit | prefixBit | suffixHit
  | separator (second : Bool) | separatorInc (second : Bool) | suffixReset
  | answer (bit : Bool)
  deriving DecidableEq, Fintype

/-- Saved boundaries and base values use the received bounded copy loop. -/
private def compCopy (C e : ℕ) : Fin 8 → Fin 14 × Fin 14 × CompState C e
  | 0 => (2, 0, .copy 1 false)
  | 1 => (3, 2, .outerDec false)
  | 2 => (8, 1, .baseInc)
  | 3 => (0, 1, .decode)
  | 4 => (4, 0, .canonical)
  | 5 => (0, 3, .canonicalDec false)
  | 6 => (8, 4, .innerHalf false)
  | 7 => (0, 4, .seek true)

/-- The outer query uses stride one; its first field uses stride two. -/
private def compStride (inner : Bool) : ℕ := if inner then 2 else 1

/-- Each shape validator stops at its previously saved physical boundary. -/
private def compLimit (inner : Bool) : Fin 14 := if inner then 3 else 1

/-- The finite chains instantiate the public aligned-pair validator. -/
private def compAdvance (C e : ℕ) (inner : Bool) (choice : Fin 4) (i : ℕ) : CompState C e :=
  if h : i < compStride inner then .scanInc inner choice ⟨i, by
    cases inner <;> simp_all [compStride]⟩
  else ![.second inner false, .second inner true, .scan inner,
    .copy (if inner then 4 else 0) false] choice

/-- The coefficient is fixed in the control, and can be zero on the inner evaluation. -/
private def compFactor (C : ℕ) (outer : Bool) : ℕ := if outer then 2 * C + 3 else C

/-- Fixed scaling uses the public transfer loop, including a zero multiplier. -/
private def compFactorAdvance (C e : ℕ) (outer : Bool) (i : ℕ) : CompState C e :=
  if h : i < compFactor C outer then .factorInc outer ⟨i, by
    cases outer <;> simp_all [compFactor]
    omega⟩ else .factorTest outer

/-- The reverse decoder has its standard two increments per transferred unit. -/
private def compDecodeAdvance (C e : ℕ) (b : Bool) (i : ℕ) : CompState C e :=
  match dropDecodeAdvance b i with
  | .decodeInc bit second => .decodeInc bit second
  | _ => .decodeScale b

/-- A single finite ARM supplies both composition-query languages. Registers 0--5 are
pointer, host length, outer-tail start, inner end, inner-tail start, and bounded query;
6--8 and 10--11 are arithmetic scratch; 12 is the searched output length and 13 the
output-position counter. Register 9 is unused. -/
private def compARM (C e : ℕ) (mode : Bool) : ARM 14 4 (CompState C e)
  | .count => .call 1 .whole [1] .countInc (.scan false)
  | .countInc => .inc 1 .count
  | .copy s false => .jeq (compCopy C e s).1 (compCopy C e s).2.1
      (compCopy C e s).2.2 (.copy s true)
  | .copy s true => .inc (compCopy C e s).1 (.copy s false)
  | .scan inner => .jeq 0 (compLimit inner) (.answer false) (.first inner)
  | .first inner => .call 0 .whole [0] (compAdvance C e inner 1 0) (compAdvance C e inner 0 0)
  | .second inner b => .jeq 0 (compLimit inner) (.answer false) (.readSecond inner b)
  | .readSecond inner b => .call 0 .whole [0]
      (if b then compAdvance C e inner 2 0 else compAdvance C e inner 3 0)
      (if b then .answer false else compAdvance C e inner 2 0)
  | .scanInc inner choice i => .inc 0 (compAdvance C e inner choice (i.val + 1))
  | .outerDec false => .dec 3 (.outerDec true)
  | .outerDec true => .dec 3 (.copy 2 false)
  | .baseInc => .inc 8 (.polyStart true)
  | .polyStart outer => .inc 7 (.power outer ⟨if outer then e + 1 else e, by
      cases outer <;> simp⟩)
  | .power outer k => .jz 6 (if k.val = 0 then .factorCopy outer false
      else .productCopy outer k false) (.answer false)
  | .productCopy outer k false => .jeq 11 7 (.productClear outer k) (.productCopy outer k true)
  | .productCopy outer k true => .inc 11 (.productCopy outer k false)
  | .productClear outer k => .clr 7 (.productTest outer k)
  | .productTest outer k => .jeq 10 8 (.productClean outer k false) (.productAddCopy outer k false)
  | .productAddCopy outer k false => .jeq 6 11 (.productAdd outer k) (.productAddCopy outer k true)
  | .productAddCopy outer k true => .inc 6 (.productAddCopy outer k false)
  | .productAdd outer k => .jz 6 (.productNext outer k) (.productTake outer k)
  | .productTake outer k => .dec 6 (.productInc outer k)
  | .productInc outer k => .inc 7 (.productAdd outer k)
  | .productNext outer k => .inc 10 (.productTest outer k)
  | .productClean outer k false => .clr 11 (.productClean outer k true)
  | .productClean outer k true => .clr 10 (.power outer ⟨k.val - 1, by omega⟩)
  | .factorCopy outer false => .jeq 11 7 (.factorClear outer) (.factorCopy outer true)
  | .factorCopy outer true => .inc 11 (.factorCopy outer false)
  | .factorClear outer => .clr 7 (.factorTest outer)
  | .factorTest outer => .jz 11 (if outer then .tailTest true else .lengthBound) (.factorDown outer)
  | .factorDown outer => .dec 11 (compFactorAdvance C e outer 0)
  | .factorInc outer i => .inc 7 (compFactorAdvance C e outer (i.val + 1))
  | .tailTest b => .jeq 0 1 (if b then .tailDone else .answer false) .tailCheck
  | .tailCheck => .jz 7 (.answer false) .tailRead
  | .tailRead => .call 0 .whole [0] (.tailHalf true) (.tailHalf false)
  | .tailHalf b => .half 7 (.tailInc b)
  | .tailInc b => .inc 0 (.tailTest b)
  | .tailDone => .clr 7 .resetDecode
  | .resetDecode => .clr 0 (.copy 3 false)
  | .decode => .jeq 0 2 .decodeDone .decodeDown
  | .decodeDown => .dec 0 .decodeRead
  | .decodeRead => .call 0 .whole [0] (.decodeCopy true false) (.decodeCopy false false)
  | .decodeCopy b false => .jeq 6 5 (.decodeClear b) (.decodeCopy b true)
  | .decodeCopy b true => .inc 6 (.decodeCopy b false)
  | .decodeClear b => .clr 5 (.decodeScale b)
  | .decodeScale b => .jz 6 (.decodeAdd b) (.decodeTake b)
  | .decodeTake b => .dec 6 (.decodeInc b false)
  | .decodeInc b false => .inc 5 (.decodeInc b true)
  | .decodeInc b true => .inc 5 (.decodeScale b)
  | .decodeAdd b => if b then .inc 5 .decode else .jz 6 .decode .decode
  | .decodeDone => .clr 0 (.scan true)
  | .canonical => .jeq 4 3 .innerPrepare .canonicalReset
  | .canonicalReset => .clr 0 (.copy 5 false)
  | .canonicalDec false => .dec 0 (.canonicalDec true)
  | .canonicalDec true => .dec 0 .canonicalRead
  | .canonicalRead => .call 0 .whole [0] .innerPrepare (.answer false)
  | .innerPrepare => .clr 8 (.copy 6 false)
  | .innerHalf false => .half 8 (.innerHalf true)
  | .innerHalf true => .half 8 (.polyStart false)
  | .lengthBound => .jeq 12 7 .doubleTest .lengthQuery
  | .lengthQuery => .call 3 .whole [12] .lengthInc .doubleTest
  | .lengthInc => .inc 12 .lengthBound
  | .doubleTest => .jz 12 .lookupReset .doubleDown
  | .doubleDown => .dec 12 (.doubleInc false)
  | .doubleInc false => .inc 11 (.doubleInc true)
  | .doubleInc true => .inc 11 .doubleTest
  | .lookupReset => .clr 0 (.seek false)
  | .seek suffix => .jeq 0 (if suffix then 3 else 11)
      (if suffix then .answer false else .separator false) (.probe suffix)
  | .probe suffix => .jeq 13 5 (if suffix then .suffixHit else .prefixHit) (.next suffix)
  | .next suffix => .inc 13 (.walk suffix false)
  | .walk suffix false => .inc 0 (if suffix then .walk suffix true else .seek suffix)
  | .walk suffix true => .inc 0 (.seek suffix)
  | .prefixHit => if mode then .ret true else .half 0 .prefixBit
  | .prefixBit => .call 2 .whole [0] (.answer true) (.answer false)
  | .suffixHit => if mode then .ret true else .call 0 .whole [0] (.answer true) (.answer false)
  | .separator false => .jeq 13 5 (.answer mode) (.separatorInc false)
  | .separator true => .jeq 13 5 (.answer true) (.separatorInc true)
  | .separatorInc false => .inc 13 (.separator true)
  | .separatorInc true => .inc 13 .suffixReset
  | .suffixReset => .clr 0 (.copy 7 false)
  | .answer b => .ret b

/-- The actual four-oracle answers, independent of the machine mode and polynomial witness. -/
private noncomputable def compOracle (f : List Bool → List Bool) (j : Fin 4) (w : List Bool) : Bool :=
  MultiTapeTM.indicator (compBank f j : Set (List Bool)) w

/-- The register bound covers both the full output cap and twice that cap for decoding. -/
private def compBound (C e n : ℕ) : ℕ := 8 * (2 * C + 3) * (n + 1) ^ (e + 1)

/-- All syntactic side conditions are independent of the input and register values.

**Proof sketch.** Inspect each finite control constructor. Calls have singleton register
lists, and copy, transfer, decoder, and comparison registers are distinct. -/
private lemma comp_preS (C e : ℕ) (mode : Bool) (h : List Bool) (a : AConf 14 (CompState C e)) :
    PreS (compARM C e mode) h a := by
  rcases a with ⟨l, v, ans⟩
  cases l with
  | none => trivial
  | some l =>
    cases l <;> simp only [PreS, compARM] <;> try decide
    case copy stage bump =>
      cases bump
      · change (compCopy C e stage).1 ≠ (compCopy C e stage).2.1
        exact (show ∀ s, (compCopy C e s).1 ≠ (compCopy C e s).2.1 by
          simp [Fin.forall_fin_succ, compCopy]) stage
      · simp
    case scan inner => cases inner <;> simp [compLimit]
    case second inner bit => cases inner <;> simp [compLimit]
    case outerDec b => cases b <;> simp
    case productCopy outer k b => cases b <;> simp
    case productAddCopy outer k b => cases b <;> simp
    case productClean outer k b => cases b <;> simp
    case factorCopy outer b => cases b <;> simp
    case decodeCopy bit b => cases b <;> simp
    case decodeInc bit b => cases b <;> simp
    case decodeAdd bit => cases bit <;> simp
    case canonicalDec b => cases b <;> simp
    case innerHalf b => cases b <;> simp
    case doubleInc b => cases b <;> simp
    case seek suffix => cases suffix <;> simp
    case walk suffix b => cases b <;> simp
    case prefixHit => cases mode <;> simp
    case suffixHit => cases mode <;> simp
    case separator b => cases b <;> simp
    case separatorInc b => cases b <;> simp

/-- A physical input bit uses exactly the already-proved access-bank law. -/
private lemma comp_bit (f : List Bool → List Bool) (h : List Bool) (i : ℕ) :
    compOracle f 0 (pairEncode h (Nat.bits i)) = h.getD i false :=
  drop_bit h i

/-- A physical input length call uses the same proved access-bank law. -/
private lemma comp_len (f : List Bool → List Bool) (h : List Bool) (i : ℕ) :
    compOracle f 1 (pairEncode h (Nat.bits i)) = decide (i < h.length) :=
  drop_len h i

/-- A genuine lifted call is answered by the received two-drop identity. -/
private lemma comp_lifted (f : List Bool → List Bool) (mode : Bool) (x b : List Bool) (p i : ℕ) :
    compOracle f (if mode then 3 else 2)
      (pairEncode (pairEncode (pairEncode x b) (Nat.bits p)) (Nat.bits i)) =
        if mode then decide (i < (f x).length) else (f x).getD i false := by
  cases mode <;> exact compLift_query f _ x b p i


/-- One common guard supplies the syntactic and register conditions to both received
run relations. -/
private abbrev CompGood (C e : ℕ) (mode : Bool) (h : List Bool) (B : ℕ) (a : AConf 14 (CompState C e)) :=
  PreS (compARM C e mode) h a ∧ ∀ r, a.2.1 r ≤ B

/-- Bounded runs use the received reachability relation, with no extra semantic assumption. -/
private abbrev CompReach (C e : ℕ) (mode : Bool) (f : List Bool → List Bool) (h : List Bool) (B : ℕ) :=
  AReach (compARM C e mode) (compOracle f) h (CompGood C e mode h B)

/-- The corresponding bounded halting assertion. -/
private abbrev CompHalt (C e : ℕ) (mode : Bool) (f : List Bool → List Bool) (h : List Bool) (B : ℕ) :=
  AHalt (compARM C e mode) (compOracle f) h (CompGood C e mode h B)

/-- The multiplication body repeatedly adds the saved multiplicand, preserving the base.

**Proof sketch.** Induct on the remaining repetition count. Each iteration invokes the
public counting copy and the public unit transfer. The final sum bounds every temporary
sum; the scratch is zero at both boundaries. -/
private lemma comp_product (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (k : Fin (e + 2)) (B : ℕ) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ B) (ht : v 6 = 0) (hi : v 10 ≤ v 8)
    (hb : v 7 + (v 8 - v 10) * v 11 ≤ B) :
    CompReach C e mode f h B (some (.productTest outer k), v, none)
      (some (.productClean outer k false),
        Function.update (Function.update v 10 (v 8)) 7
          (v 7 + (v 8 - v 10) * v 11), none) := by
  generalize he : v 8 - v 10 = left
  induction left generalizing v with
  | zero =>
    have eq : v 10 = v 8 := by omega
    have up : Function.update v 10 (v 8) = v := by rw [← eq, Function.update_eq_self]
    simp only [Nat.zero_mul, Nat.add_zero, up, Function.update_eq_self]
    simpa [astep_jeq (show compARM C e mode (.productTest outer k) = _ from rfl), eq] using
      (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (a := (some (.productTest outer k), v, none)) ⟨comp_preS C e mode h _, hv⟩)
  | succ left ih =>
    have lt : v 10 < v 8 := by omega
    have total : v 7 + v 11 + left * v 11 ≤ B := by
      rw [he, Nat.succ_mul] at hb
      omega
    let vc := Function.update v 6 (v 11)
    let va := Function.update v 7 (v 7 + v 11)
    let vn := Function.update va 10 (v 10 + 1)
    have bc : ∀ r, vc r ≤ B := register_update_le v 6 B _ hv (hv 11)
    have ba : ∀ r, va r ≤ B := register_update_le v 7 B _ hv (by omega)
    have bn : ∀ r, vn r ≤ B := register_update_le va 10 B _ ba (by have := hv 8; omega)
    have cp := registerCopy_loop (compARM C e mode) (compOracle f) h 6 11 (by decide)
      (.productAddCopy outer k false) (.productAddCopy outer k true) (.productAdd outer k)
      rfl rfl B v hv (by rw [ht]; exact Nat.zero_le _)
    have add := registerScale_loop (compARM C e mode) (compOracle f) h 6 7 (by decide)
      (.productAdd outer k) (.productTake outer k) (.productNext outer k)
      (fun i => if i = 0 then .productInc outer k else .productAdd outer k) 1
      rfl rfl (by
        intro i hi
        have hz : i = 0 := by omega
        subst i
        rfl) rfl B vc bc
      (by simp [vc]; omega)
    have addend : Function.update (Function.update vc 6 0) 7 (vc 7 + 1 * vc 6) = va := by
      simp [vc, va, ← ht, Function.update_eq_self]
    rw [addend] at add
    have rest := ih vn bn (by simp [vn, va, ht]) (by simp [vn, va]; omega)
      (by simp only [vn, va, Function.update_self, Function.update_of_ne (by decide : (8 : Fin 14) ≠ 10),
          Function.update_of_ne (by decide : (8 : Fin 14) ≠ 7),
          Function.update_of_ne (by decide : (7 : Fin 14) ≠ 10),
          Function.update_of_ne (by decide : (11 : Fin 14) ≠ 10),
          Function.update_of_ne (by decide : (11 : Fin 14) ≠ 7)]
          have eq : v 8 - (v 10 + 1) = left := by omega
          rw [eq]; exact total)
      (by simp [vn, va]; omega)
    have endeq : Function.update (Function.update vn 10 (vn 8)) 7
        (vn 7 + left * vn 11) =
        Function.update (Function.update v 10 (v 8)) 7
          (v 7 + (left + 1) * v 11) := by
      funext r
      by_cases h7 : r = 7
      · subst r; simp [vn, va, Nat.succ_mul]; omega
      · by_cases h10 : r = 10
        · subst r; simp [vn, va]
        · simp [vn, va, Function.update_of_ne, h7, h10]
    rw [endeq] at rest
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep_jeq (show compARM C e mode (.productTest outer k) = _ from rfl),
      if_neg (Nat.ne_of_lt lt)]
    apply cp.trans
    apply add.trans
    apply AReach.step ⟨comp_preS C e mode h _, ba⟩
    simpa only [astep_inc (show compARM C e mode (.productNext outer k) = _ from rfl), va,
      Function.update_of_ne (by decide : (10 : Fin 14) ≠ 7)] using rest


/-- One power round multiplies the accumulator by its base and restores all scratch.

**Proof sketch.** Save the old accumulator with the shared copy, clear the destination,
invoke the proved repeated-addition loop, and clear its two counters. -/
private lemma comp_multiply (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (k : Fin (e + 2)) (B : ℕ) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ B) (ht : v 6 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hb : v 7 * v 8 ≤ B) :
    CompReach C e mode f h B (some (.productCopy outer k false), v, none)
      (some (.power outer ⟨k.val - 1, by omega⟩), Function.update v 7 (v 7 * v 8), none) := by
  let vc := Function.update v 11 (v 7)
  let vz := Function.update vc 7 0
  let ve := Function.update (Function.update vz 10 (v 8)) 7 (v 7 * v 8)
  have bc : ∀ r, vc r ≤ B := register_update_le v 11 B _ hv (hv 7)
  have bz : ∀ r, vz r ≤ B := register_update_le vc 7 B 0 bc (Nat.zero_le _)
  have be : ∀ r, ve r ≤ B := register_update_le _ 7 B _
    (register_update_le vz 10 B _ bz (hv 8)) hb
  have cp := registerCopy_loop (compARM C e mode) (compOracle f) h 11 7 (by decide)
    (.productCopy outer k false) (.productCopy outer k true) (.productClear outer k)
    rfl rfl B v hv (by rw [hs]; exact Nat.zero_le _)
  have body : CompReach C e mode f h B (some (.productTest outer k), vz, none)
      (some (.productClean outer k false), ve, none) := by
    simpa [vz, vc, ve, hi, Nat.mul_comm] using
      comp_product C e mode outer f h k B vz bz (by simp [vz, vc, ht])
        (by simp [vz, vc, hi]) (by simpa [vz, vc, hi, Nat.mul_comm] using hb)
  have clean : CompReach C e mode f h B (some (.productClean outer k false), ve, none)
      (some (.power outer ⟨k.val - 1, by omega⟩), Function.update v 7 (v 7 * v 8), none) := by
    apply AReach.step ⟨comp_preS C e mode h _, be⟩
    simp only [astep_clr (show compARM C e mode (.productClean outer k false) = _ from rfl)]
    have bound := register_update_le ve 11 B 0 be (Nat.zero_le _)
    have last := AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
      (G := fun a => PreS (compARM C e mode) h a ∧ ∀ r, a.2.1 r ≤ B)
      (a := (some (.productClean outer k true), Function.update ve 11 0, none))
      ⟨comp_preS C e mode h _, bound⟩
    have eq : Function.update (Function.update ve 11 0) 10 0 = Function.update v 7 (v 7 * v 8) := by
      funext r
      by_cases h7 : r = 7
      · subst r; simp [ve]
      · by_cases h10 : r = 10
        · subst r; simp [hi]
        · by_cases h11 : r = 11
          · subst r; simp [hs]
          · simp [ve, vz, vc, Function.update_of_ne, h7, h10, h11]
    simpa only [astep_clr (show compARM C e mode (.productClean outer k true) = _ from rfl),
      eq] using last
  apply cp.trans
  apply AReach.step ⟨comp_preS C e mode h _, bc⟩
  exact body.trans clean

/-- The final constant scaling shares the proved transfer loop, even when the coefficient
is zero. Scratch register 11 is restored to zero.

**Proof sketch.** Copy the accumulator to the saved multiplicand, clear its destination,
apply `registerScale_loop` at the fixed coefficient, and clear the remaining scratch. -/
private lemma comp_factor_run (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hs : v 11 = 0) (hb : compFactor C outer * v 7 ≤ B) :
    CompReach C e mode f h B (some (.factorCopy outer false), v, none)
      (some (if outer then .tailTest true else .lengthBound),
        Function.update v 7 (compFactor C outer * v 7), none) := by
  let vc := Function.update v 11 (v 7)
  let vz := Function.update vc 7 0
  have bc : ∀ r, vc r ≤ B := register_update_le v 11 B _ hv (hv 7)
  have bz : ∀ r, vz r ≤ B := register_update_le vc 7 B 0 bc (Nat.zero_le _)
  have cp := registerCopy_loop (compARM C e mode) (compOracle f) h 11 7 (by decide)
    (.factorCopy outer false) (.factorCopy outer true) (.factorClear outer)
    rfl rfl B v hv (by rw [hs]; exact Nat.zero_le _)
  have scale := registerScale_loop (compARM C e mode) (compOracle f) h 11 7 (by decide)
    (.factorTest outer) (.factorDown outer) (if outer then .tailTest true else .lengthBound)
    (compFactorAdvance C e outer) (compFactor C outer) rfl rfl
    (by intro i hi; simp only [compFactorAdvance, dif_pos hi, compARM])
    (by simp [compFactorAdvance]) B vz bz (by simpa [vz, vc] using hb)
  have eq : Function.update (Function.update vz 11 0) 7
      (vz 7 + compFactor C outer * vz 11) = Function.update v 7 (compFactor C outer * v 7) := by
    funext r
    by_cases h7 : r = 7
    · subst r; simp [vz, vc]
    · by_cases h11 : r = 11
      · subst r; simp [hs]
      · simp [vz, vc, Function.update_of_ne, h7, h11]
  rw [eq] at scale
  apply cp.trans
  apply AReach.step ⟨comp_preS C e mode h _, bc⟩
  exact scale

/-- The power subprogram has a polynomial bound on every intermediate value.

**Proof sketch.** Induct on the remaining exponent. A nonzero exponent invokes one
multiplication round; its result is no larger than the final power because the base is
at least one. At zero, apply the fixed-scaling contract. -/
private lemma comp_power_run (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (k : Fin (e + 2)) (B : ℕ) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ B) (ht : v 6 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hbase : 1 ≤ v 8) (hp : v 7 * v 8 ^ k.val ≤ B)
    (hf : compFactor C outer * (v 7 * v 8 ^ k.val) ≤ B) :
    CompReach C e mode f h B (some (.power outer k), v, none)
      (some (if outer then .tailTest true else .lengthBound),
        Function.update v 7 (compFactor C outer * (v 7 * v 8 ^ k.val)), none) := by
  generalize hn : k.val = n
  induction n generalizing k v with
  | zero =>
    simp only [pow_zero, Nat.mul_one]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep_jz (show compARM C e mode (.power outer k) = _ from rfl), ht, ↓reduceIte, hn]
    exact comp_factor_run C e mode outer f h B v hv hs (by simpa [hn] using hf)
  | succ n ih =>
    let vn := Function.update v 7 (v 7 * v 8)
    have prod : v 7 * v 8 ≤ B := by
      apply Nat.le_trans _ hp
      apply Nat.mul_le_mul_left
      rw [hn]
      calc v 8 = v 8 ^ 1 := (pow_one _).symm
        _ ≤ v 8 ^ (n + 1) := Nat.pow_le_pow_right hbase (by omega)
    have bn : ∀ r, vn r ≤ B := register_update_le v 7 B _ hv prod
    have power : vn 7 * vn 8 ^ n = v 7 * v 8 ^ (n + 1) := by
      simp only [vn, Function.update_self, Function.update_of_ne (by decide : (8 : Fin 14) ≠ 7), pow_succ]
      ring
    let kn : Fin (e + 2) := ⟨k.val - 1, by omega⟩
    have knv : kn.val = n := by dsimp [kn]; omega
    have rest := ih kn vn bn (by simp [vn, ht]) (by simp [vn, hi]) (by simp [vn, hs])
      (by simpa [vn] using hbase)
      (by rw [knv, power, ← hn]; exact hp)
      (by rw [knv, power, ← hn]; exact hf) knv
    have endeq : Function.update vn 7 (compFactor C outer * (vn 7 * vn 8 ^ n)) =
        Function.update v 7 (compFactor C outer * (v 7 * v 8 ^ (n + 1))) := by
      rw [power]; simp only [vn, Function.update_idem]
    rw [endeq] at rest
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep_jz (show compARM C e mode (.power outer k) = _ from rfl), ht, hn,
      Nat.succ_ne_zero, ↓reduceIte]
    exact (comp_multiply C e mode outer f h k B v hv ht hi hs prod).trans rest


/-- Starting from cleared scratch, the shared polynomial routine computes its exact cap.
The inner coefficient may be zero; the routine still halts and returns zero. -/
private lemma comp_poly_run (C e : ℕ) (mode outer : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (ht : v 6 = 0) (ha : v 7 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hbase : 1 ≤ v 8) (hp : v 8 ^ (if outer then e + 1 else e) ≤ B)
    (hf : compFactor C outer * v 8 ^ (if outer then e + 1 else e) ≤ B) :
    CompReach C e mode f h B (some (.polyStart outer), v, none)
      (some (if outer then .tailTest true else .lengthBound),
        Function.update v 7 (compFactor C outer * v 8 ^ (if outer then e + 1 else e)), none) := by
  let vn := Function.update v 7 1
  have hb : 1 ≤ B := (Nat.one_le_pow _ _ hbase).trans hp
  have bn := register_update_le v 7 B 1 hv hb
  have run := comp_power_run C e mode outer f h
    ⟨if outer then e + 1 else e, by cases outer <;> simp⟩ B vn bn
    (by simp [vn, ht]) (by simp [vn, hi]) (by simp [vn, hs])
    (by simpa [vn] using hbase) (by simpa [vn] using hp) (by simpa [vn] using hf)
  apply AReach.step ⟨comp_preS C e mode h _, hv⟩
  simpa [astep_inc (show compARM C e mode (.polyStart outer) = _ from rfl), ha, vn] using run

/-- Every required power, at either base and coefficient, fits the full output cap. -/
private lemma comp_power_bound (C e n base exponent : ℕ) (outer : Bool)
    (hb : base ≤ n + 1) (he : exponent ≤ e + 1) :
    base ^ exponent ≤ compBound C e n ∧
      compFactor C outer * base ^ exponent ≤ compBound C e n := by
  have pp : base ^ exponent ≤ (n + 1) ^ (e + 1) :=
    (Nat.pow_le_pow_left hb _).trans (Nat.pow_le_pow_right (by omega) he)
  have cf : compFactor C outer ≤ 8 * (2 * C + 3) := by
    cases outer <;> simp only [compFactor, Bool.false_eq_true, ↓reduceIte] <;> omega
  constructor
  · exact pp.trans (Nat.le_mul_of_pos_left _ (by omega))
  · exact Nat.mul_le_mul cf pp

/-- Twice the full cap and all physical addresses fit the common polynomial bound. -/
private lemma comp_bound_room (C e n : ℕ) :
    n + 1 ≤ compBound C e n ∧ 2 * ((2 * C + 3) * (n + 1) ^ (e + 1)) ≤ compBound C e n := by
  constructor
  · have base : n + 1 ≤ (n + 1) ^ (e + 1) := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact base.trans (Nat.le_mul_of_pos_left _ (by omega))
  · unfold compBound
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (by omega)

/-- A capped length search never queries the cap itself. It stops at the first false
answer, or returns the cap if every smaller answer is true.

**Proof sketch.** The current counter is at most the true length, itself at most the cap.
If the counter equals the cap, it equals the length and exits without a query. Otherwise,
the truthful length query either exits at equality or permits one bounded increment.
Induct on the distance to the true length. This includes cap zero. -/
private lemma comp_length_search (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B F : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hi : v 12 ≤ F) (hc : F ≤ v 7)
    (ho : ∀ i < v 7, compOracle f 3 (pairEncode h (Nat.bits i)) = decide (i < F)) :
    CompReach C e mode f h B (some .lengthBound, v, none)
      (some .doubleTest, Function.update v 12 F, none) := by
  generalize he : F - v 12 = left
  induction left generalizing v with
  | zero =>
    have eq : v 12 = F := by omega
    have vu : Function.update v 12 F = v := by rw [← eq, Function.update_eq_self]
    rw [vu]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep_jeq (show compARM C e mode .lengthBound = _ from rfl)]
    by_cases cap : v 12 = v 7
    · simp only [if_pos cap]; exact AReach.refl _
    · simp only [if_neg cap]
      have ans := ho (v 12) (by omega)
      simp only [eq, lt_self_iff_false, decide_false] at ans
      simpa [astep_call (show compARM C e mode .lengthQuery = _ from rfl), eq, ans,
        vword_whole₁] using
        (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
          (a := (some .lengthQuery, v, none)) ⟨comp_preS C e mode h _, hv⟩)
  | succ left ih =>
    have lt : v 12 < F := by omega
    have cap : v 12 ≠ v 7 := by omega
    let vn := Function.update v 12 (v 12 + 1)
    have bn : ∀ r, vn r ≤ B := register_update_le v 12 B _ hv (by have := hv 7; omega)
    have rest := ih vn bn (by simp [vn]; omega) (by simpa [vn] using hc)
      (by simpa [vn] using ho) (by simp [vn]; omega)
    have ans := ho (v 12) (by omega)
    simp only [lt, decide_true] at ans
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep_jeq (show compARM C e mode .lengthBound = _ from rfl), if_neg cap]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep_call (show compARM C e mode .lengthQuery = _ from rfl), vword_whole₁, ans,
      ↓reduceIte]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simpa only [astep_inc (show compARM C e mode .lengthInc = _ from rfl), vn,
      Function.update_idem] using rest


/-- Boundary vectors keep the physical positions separate from the bounded query and
arithmetic scratch. -/
private def compValues (n : ℕ) (ptr tail stop inner query temp cap base spare iter old len idx : ℕ := 0) :
    Fin 14 → ℕ := ![ptr, n, tail, stop, inner, query, temp, cap, base, spare, iter, old, len, idx]

/-- Coordinate lookup exposes the vector without unfolding it under an update. -/
@[simp] private lemma compValues_apply (n p a w b q t c x s i y l j : ℕ) (r : Fin 14) :
    compValues n p a w b q t c x s i y l j r = ![p, n, a, w, b, q, t, c, x, s, i, y, l, j] r := rfl

/-- A single update changes just the named coordinate of a boundary vector. -/
@[simp] private lemma compValues_update (n p a w b q t c x s i y l j : ℕ) (r : Fin 14) (v : ℕ) :
    Function.update (compValues n p a w b q t c x s i y l j) r v =
      compValues (if 1 = r then v else n) (if 0 = r then v else p)
        (if 2 = r then v else a) (if 3 = r then v else w) (if 4 = r then v else b)
        (if 5 = r then v else q) (if 6 = r then v else t) (if 7 = r then v else c)
        (if 8 = r then v else x) (if 9 = r then v else s) (if 10 = r then v else i)
        (if 11 = r then v else y) (if 12 = r then v else l) (if 13 = r then v else j) := by
  revert r
  simp [Fin.forall_fin_succ, compValues, Matrix.vecCons, Fin.update_cons_zero, ← Fin.cons_update]

/-- The copy stages are all instances of the proved counting copy. -/
private lemma comp_copy_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (stage : Fin 8) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ B) (hle : v (compCopy C e stage).1 ≤ v (compCopy C e stage).2.1) :
    CompReach C e mode f h B (some (.copy stage false), v, none)
      (some (compCopy C e stage).2.2,
        Function.update v (compCopy C e stage).1 (v (compCopy C e stage).2.1), none) := by
  have ne : ∀ s, (compCopy C e s).1 ≠ (compCopy C e s).2.1 := by
    simp [Fin.forall_fin_succ, compCopy]
  apply registerCopy_loop (compARM C e mode) (compOracle f) h _ _ (ne stage)
    _ _ _ rfl rfl B v hv hle

/-- Both shape scans cite the same public strided validator; no field canonicality is
imposed by this fragment.

**Proof sketch.** Instantiate `alignedPair_loop` at the selected stride and saved end
register. The finite increment chains discharge its transition equations. -/
private lemma comp_pair_run (C e : ℕ) (mode inner : Bool) (f : List Bool → List Bool)
    (h w : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hl : v (compLimit inner) = v 0 + compStride inner * w.length)
    (ho : ∀ i < w.length, h.getD (v 0 + compStride inner * i) false = w.getD i false) :
    match pairDecode w with
    | none => ∃ t ≤ w.length, CompReach C e mode f h B (some (.scan inner), v, none)
        (some (.answer false), Function.update v 0 (v 0 + compStride inner * t), none)
    | some (a, _) => CompReach C e mode f h B (some (.scan inner), v, none)
        (some (.copy (if inner then 4 else 0) false),
          Function.update v 0 (v 0 + compStride inner * (2 * a.length + 2)), none) := by
  apply alignedPair_loop (compARM C e mode) (compOracle f) h 0 (compLimit inner) 0
    (.scan inner) (.first inner) (.second inner) (.readSecond inner)
    (.answer false) (.copy (if inner then 4 else 0) false) (compAdvance C e inner)
    (compStride inner) B (by cases inner <;> decide) (by cases inner <;> decide)
    rfl rfl (fun _ => rfl) (fun _ => rfl)
  · intro choice i hi
    simp only [compAdvance, dif_pos hi, compARM]
  · simp [compAdvance]
  · exact hv
  · exact hl
  · intro i hi
    rw [comp_bit]
    exact ho i hi

/-- Returning at an answer node takes one bounded step. -/
private lemma comp_ret (C e : ℕ) (mode b : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B) :
    CompHalt C e mode f h B (some (.answer b), v, none) b :=
  AHalt.ret rfl ⟨comp_preS C e mode h _, hv⟩

/-- The suffix of the inner pair is read at doubled physical addresses. -/
private lemma comp_suffix_address (x b tail : List Bool) (j : ℕ) (hj : j < b.length) :
    (pairEncode (pairEncode x b) tail).getD (4 * x.length + 4 + 2 * j) false = b.getD j false := by
  have len := length_pairEncode x b
  rw [pairEncode_getD, if_pos (by omega)]
  have div : (4 * x.length + 4 + 2 * j) / 2 = 2 * x.length + 2 + j := by omega
  rw [div, pairEncode_getD_snd]

/-- For a nonempty inner field, its final physical bit is exactly its canonicality flag.
The field's represented number is never computed. -/
private lemma comp_last_address (x b tail : List Bool) (hb : b ≠ []) :
    (pairEncode (pairEncode x b) tail).getD (2 * (pairEncode x b).length - 2) false =
      b.getLastD true := by
  have pos : 0 < b.length := List.length_pos_iff.mpr hb
  have addr : 2 * (pairEncode x b).length - 2 = 4 * x.length + 4 + 2 * (b.length - 1) := by
    rw [length_pairEncode]; omega
  rw [addr, comp_suffix_address x b tail _ (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by omega : b.length - 1 < b.length)]

/-- The inner canonicality check inspects the empty-field boundary or its last bit.
Only the physical pointer changes; no numerical bound is imposed on the inner payload.

**Proof sketch.** Equality of the saved boundaries accepts the empty field. Otherwise,
copy the inner end, move back two physical cells, and read the last suffix bit. Its value
is exactly the empty-or-final-true canonicality predicate. -/
private lemma comp_canonical_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b tail : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (he : v 3 = 2 * (pairEncode x b).length) (hb : v 4 = 4 * x.length + 4) :
    ∃ v', (∀ r, v' r ≤ B) ∧ (∀ r, r ≠ 0 → v' r = v r) ∧
      CompReach C e mode f (pairEncode (pairEncode x b) tail) B
        (some .canonical, v, none)
        (some (if Canon b then .innerPrepare else .answer false), v', none) := by
  let h := pairEncode (pairEncode x b) tail
  by_cases empty : b = []
  · subst b
    have eq : v 4 = v 3 := by rw [hb, he, length_pairEncode]; simp only [List.length_nil]; omega
    refine ⟨v, hv, fun _ _ => rfl, ?_⟩
    simpa [astep_jeq (show compARM C e mode .canonical = _ from rfl), eq, Canon] using
      (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (a := (some .canonical, v, none)) ⟨comp_preS C e mode h _, hv⟩)
  · have pos : 0 < b.length := List.length_pos_iff.mpr empty
    have ne : v 4 ≠ v 3 := by rw [hb, he, length_pairEncode]; omega
    let vz := Function.update v 0 0
    let vc := Function.update v 0 (v 3)
    let vd := Function.update v 0 (v 3 - 1)
    let vf := Function.update v 0 (v 3 - 2)
    have bz := register_update_le v 0 B 0 hv (Nat.zero_le _)
    have bc := register_update_le v 0 B (v 3) hv (hv 3)
    have bd := register_update_le v 0 B (v 3 - 1) hv (by have := hv 3; omega)
    have bf := register_update_le v 0 B (v 3 - 2) hv (by have := hv 3; omega)
    refine ⟨vf, bf, fun r hr => Function.update_of_ne hr _ _, ?_⟩
    have cp : CompReach C e mode f h B (some (.copy 5 false), vz, none)
        (some (.canonicalDec false), vc, none) := by
      simpa [vz, vc, compCopy] using comp_copy_run C e mode f h B 5 vz bz (by simp [vz, compCopy])
    have read : compOracle f 0 (pairEncode h (Nat.bits (vf 0))) = b.getLastD true := by
      rw [comp_bit]
      simpa [vf, h, he] using comp_last_address x b tail empty
    have last : CompReach C e mode f h B (some .canonicalRead, vf, none)
        (some (if Canon b then .innerPrepare else .answer false), vf, none) := by
      have step := AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (G := fun a => PreS (compARM C e mode) h a ∧ ∀ r, a.2.1 r ≤ B)
        (a := (some .canonicalRead, vf, none)) ⟨comp_preS C e mode h _, bf⟩
      simpa only [astep_call (show compARM C e mode .canonicalRead = _ from rfl), vword_whole₁,
        read, drop_canon] using step
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep_jeq (show compARM C e mode .canonical = _ from rfl), if_neg ne]
    apply AReach.step ⟨comp_preS C e mode h _, hv⟩
    simp only [astep_clr (show compARM C e mode .canonicalReset = _ from rfl)]
    apply cp.trans
    apply AReach.step ⟨comp_preS C e mode h _, bc⟩
    simp only [astep_dec (show compARM C e mode (.canonicalDec false) = _ from rfl), vc,
      Function.update_self, Function.update_idem]
    apply AReach.step ⟨comp_preS C e mode h _, bd⟩
    simpa only [astep_dec (show compARM C e mode (.canonicalDec true) = _ from rfl), vd, vf,
      Function.update_self, Function.update_idem,
      Nat.sub_sub, Nat.reduceAdd] using last


/-- After the outer shape scan, save its boundaries and construct the full output cap.

**Proof sketch.** The separator end gives the outer tail and, after two decrements, the
inner end. Copy the physical host length and increment to obtain the power base. The
shared polynomial routine supplies the full composition cap before any index decoding. -/
private lemma comp_outer_prepare (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (z tail : List Bool) :
    let h := pairEncode z tail
    let a := 2 * z.length + 2
    CompReach C e mode f h (compBound C e h.length)
      (some (.copy 0 false), compValues h.length (ptr := a), none)
      (some (.tailTest true), compValues h.length (ptr := a) (tail := a)
        (stop := 2 * z.length) (cap := (2 * C + 3) * (h.length + 1) ^ (e + 1))
        (base := h.length + 1), none) := by
  dsimp only
  let h := pairEncode z tail
  let a := 2 * z.length + 2
  let B := compBound C e h.length
  have room := (comp_bound_room C e h.length).1
  have ab : a ≤ h.length := by dsimp [a, h]; rw [length_pairEncode]; omega
  have bounds : ∀ p t w b, p ≤ h.length + 1 → t ≤ h.length + 1 → w ≤ h.length + 1 →
      b ≤ h.length + 1 → ∀ r, (compValues h.length (ptr := p) (tail := t) (stop := w) (base := b)) r ≤ B := by
    intro p t w b hp ht hw hb
    simp [Fin.forall_fin_succ, compValues]
    dsimp [B] at *
    omega
  let v₀ := compValues h.length (ptr := a)
  let v₁ := compValues h.length (ptr := a) (tail := a)
  let v₂ := compValues h.length (ptr := a) (tail := a) (stop := a)
  let v₃ := compValues h.length (ptr := a) (tail := a) (stop := a - 1)
  let v₄ := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length)
  let v₅ := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length) (base := h.length)
  let v₆ := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length) (base := h.length + 1)
  have b₀ : ∀ r, v₀ r ≤ B := bounds a 0 0 0 (by omega) (by omega) (by omega) (by omega)
  have b₁ : ∀ r, v₁ r ≤ B := bounds a a 0 0 (by omega) (by omega) (by omega) (by omega)
  have b₂ : ∀ r, v₂ r ≤ B := bounds a a a 0 (by omega) (by omega) (by omega) (by omega)
  have b₃ : ∀ r, v₃ r ≤ B := bounds a a (a-1) 0 (by omega) (by omega) (by omega) (by omega)
  have b₄ : ∀ r, v₄ r ≤ B := bounds a a (2*z.length) 0 (by omega) (by omega) (by dsimp [a] at ab; omega) (by omega)
  have b₅ : ∀ r, v₅ r ≤ B := bounds a a (2*z.length) h.length (by omega) (by omega) (by dsimp [a] at ab; omega) (by omega)
  have b₆ : ∀ r, v₆ r ≤ B := bounds a a (2*z.length) (h.length+1) (by omega) (by omega) (by dsimp [a] at ab; omega) le_rfl
  have c₀ : CompReach C e mode f h B (some (.copy 0 false), v₀, none)
      (some (.copy 1 false), v₁, none) := by
    simpa [v₀, v₁, compCopy] using comp_copy_run C e mode f h B 0 v₀ b₀ (by simp [v₀, compCopy])
  have c₁ : CompReach C e mode f h B (some (.copy 1 false), v₁, none)
      (some (.outerDec false), v₂, none) := by
    simpa [v₁, v₂, compCopy] using comp_copy_run C e mode f h B 1 v₁ b₁ (by simp [v₁, compCopy])
  have c₂ : CompReach C e mode f h B (some (.outerDec false), v₂, none)
      (some (.copy 2 false), v₄, none) := by
    apply AReach.step ⟨comp_preS C e mode h _, b₂⟩
    simp only [astep_dec (show compARM C e mode (.outerDec false) = _ from rfl)]
    rw [show Function.update v₂ 3 (v₂ 3 - 1) = v₃ by simp [v₂, v₃]]
    apply AReach.step ⟨comp_preS C e mode h _, b₃⟩
    simpa [astep_dec (show compARM C e mode (.outerDec true) = _ from rfl), v₃, v₄, a] using
      (AReach.refl (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (G := fun a => PreS (compARM C e mode) h a ∧ ∀ r, a.2.1 r ≤ B)
        (some (.copy 2 false), v₄, none))
  have c₃ : CompReach C e mode f h B (some (.copy 2 false), v₄, none)
      (some .baseInc, v₅, none) := by
    simpa [v₄, v₅, compCopy] using comp_copy_run C e mode f h B 2 v₄ b₄ (by simp [v₄, compCopy])
  have pp := comp_power_bound C e h.length (h.length + 1) (e + 1) true le_rfl le_rfl
  have pol := comp_poly_run C e mode true f h B v₆ b₆
    (by simp [v₆, compValues]) (by simp [v₆, compValues]) (by simp [v₆, compValues])
    (by simp [v₆, compValues]) (by simp [v₆, compValues])
    (by simpa [v₆, compValues] using pp.1) (by simpa [v₆, compValues] using pp.2)
  apply (c₀.trans (c₁.trans (c₂.trans c₃))).trans
  apply AReach.step ⟨comp_preS C e mode h _, b₅⟩
  simpa [astep_inc (show compARM C e mode .baseInc = _ from rfl), v₅, v₆, compFactor] using pol

/-- The bounded outer tail is validated before its numeric value is accumulated.

**Proof sketch.** Apply the shared canonical tail scan against the full composition cap.
Failure returns false. On success, clear the consumed cap, restore the pointer to the
host end, and invoke the shared reverse decoder. The frozen suffix-value bound applies
at every decode step. Finally clear the pointer for the inner shape scan. -/
private lemma comp_outer_decode (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (z tail : List Bool) :
    let h := pairEncode z tail
    let a := 2 * z.length + 2
    let cap := (2 * C + 3) * (h.length + 1) ^ (e + 1)
    let v := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length)
      (cap := cap) (base := h.length + 1)
    if Canon tail ∧ tail.length ≤ (Nat.bits cap).length then
      CompReach C e mode f h (compBound C e h.length) (some (.tailTest true), v, none)
        (some (.scan true), compValues h.length (tail := a) (stop := 2 * z.length)
          (query := bitsVal tail) (base := h.length + 1), none)
    else CompHalt C e mode f h (compBound C e h.length) (some (.tailTest true), v, none) false := by
  dsimp only
  let h := pairEncode z tail
  let a := 2 * z.length + 2
  let cap := (2 * C + 3) * (h.length + 1) ^ (e + 1)
  let B := compBound C e h.length
  let v₀ := compValues h.length (ptr := a) (tail := a) (stop := 2 * z.length)
    (cap := cap) (base := h.length + 1)
  have len : h.length = a + tail.length := length_pairEncode z tail
  have room := comp_bound_room C e h.length
  have b₀ : ∀ r, v₀ r ≤ B := by
    simp [v₀, compValues, Fin.forall_fin_succ]
    dsimp [a, B, cap] at *
    omega
  have reads : ∀ i < tail.length, compOracle f 0 (pairEncode h (Nat.bits (v₀ 0 + 1 * i))) = tail.getD i false := by
    intro i hi
    rw [comp_bit]
    simp only [v₀, compValues, Matrix.cons_val_zero, Nat.one_mul]
    rw [show h = pairEncode z tail by rfl, pairEncode_getD]
    rw [if_neg (by dsimp [a]; omega), if_neg (by dsimp [a]; omega), if_neg (by dsimp [a]; omega)]
    congr 1
    dsimp [a]; omega
  obtain ⟨vs, bs, ps, frame, scan⟩ := canonicalTail_loop (compARM C e mode) (compOracle f) h
    0 1 7 (by decide) (by decide) (by decide) 0 CompState.tailTest
    .tailCheck .tailRead (.answer false) .tailDone CompState.tailHalf
    (fun b i => if i = 0 then .tailInc b else .tailTest b) 1 B (by omega)
    (fun _ => rfl) rfl rfl (fun _ => rfl)
    (by
      intro b i hi
      have hz : i = 0 := by omega
      subst i
      rfl)
    (fun _ => rfl) tail true v₀ b₀ (by simpa [v₀, compValues] using len) reads
  by_cases good : Canon tail ∧ tail.length ≤ (Nat.bits cap).length
  · rw [if_pos good]
    have scan' : CompReach C e mode f h B (some (.tailTest true), v₀, none) (some .tailDone, vs, none) := by
      have flag := (drop_canon tail).mpr good.1
      simp only [flag, ↓reduceIte] at scan
      simpa [v₀, good.2] using scan
    let vz := compValues h.length (tail := a) (stop := 2*z.length) (base := h.length+1)
    let vd := compValues h.length (ptr := h.length) (tail := a) (stop := 2*z.length) (base := h.length+1)
    have bz : ∀ r, vz r ≤ B := by
      simp [vz, compValues, Fin.forall_fin_succ]; dsimp [a, B] at *; omega
    have bd : ∀ r, vd r ≤ B := by
      simp [vd, compValues, Fin.forall_fin_succ]; dsimp [a, B] at *; omega
    have reset : CompReach C e mode f h B (some .tailDone, vs, none) (some (.copy 3 false), vz, none) := by
      apply AReach.step ⟨comp_preS C e mode h _, bs⟩
      simp only [astep_clr (show compARM C e mode .tailDone = _ from rfl)]
      apply AReach.step ⟨comp_preS C e mode h _, register_update_le vs 7 B 0 bs (Nat.zero_le _)⟩
      simp only [astep_clr (show compARM C e mode .resetDecode = _ from rfl)]
      have ve : Function.update (Function.update vs 7 0) 0 0 = vz := by
        apply funext
        simp only [Fin.forall_fin_succ] at frame ⊢
        simp_all [vz, v₀, compValues, Function.update_apply]
      rw [ve]
      exact AReach.refl _
    have copy : CompReach C e mode f h B (some (.copy 3 false), vz, none) (some .decode, vd, none) := by
      simpa [vz, vd, compCopy] using comp_copy_run C e mode f h B 3 vz bz (by simp [vz, compCopy])
    have values : ∀ i ≤ tail.length, bitsVal (tail.drop i) ≤ B := by
      intro i _
      exact (query_accumulator_bound tail cap i good.1 good.2).trans room.2
    have dread : ∀ i < tail.length, compOracle f 0 (pairEncode h (Nat.bits (vd 2 + i))) = tail.getD i false := by
      simpa [vd, v₀, compValues] using reads
    obtain ⟨vf, bf, fp, fq, ft, ff, dec⟩ := boundedDecode_loop (compARM C e mode) (compOracle f) h
      0 2 5 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      0 .decode .decodeDown .decodeRead .decodeDone
      (fun b => .decodeCopy b false) (fun b => .decodeCopy b true) CompState.decodeClear
      CompState.decodeScale CompState.decodeTake CompState.decodeAdd (compDecodeAdvance C e)
      rfl rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (by
        intro b i hi
        have cases : i = 0 ∨ i = 1 := by omega
        rcases cases with rfl | rfl <;> rfl)
      (fun _ => rfl) (fun _ => rfl) tail B values tail.length le_rfl vd bd
      (by simpa [vd, compValues] using len) (by simp [vd, compValues, bitsVal])
      (by simp [vd, compValues]) dread
    have endv : Function.update vf 0 0 = compValues h.length (tail := a) (stop := 2*z.length)
        (query := bitsVal tail) (base := h.length+1) := by
      apply funext
      simp only [Fin.forall_fin_succ] at ff ⊢
      simp_all [vd, compValues]
    apply (scan'.trans (reset.trans (copy.trans dec))).trans
    simpa only [astep_clr (show compARM C e mode .decodeDone = _ from rfl), endv] using
      (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
        (a := (some .decodeDone, vf, none)) ⟨comp_preS C e mode h _, bf⟩)
  · rw [if_neg good]
    have scan' : CompReach C e mode f h B (some (.tailTest true), v₀, none) (some (.answer false), vs, none) := by
      by_cases width : tail.length ≤ (Nat.bits cap).length
      · have canon : ¬ Canon tail := fun hc => good ⟨hc, width⟩
        have last : tail.getLastD true = false := Bool.eq_false_iff.mpr (fun hc => canon ((drop_canon tail).mp hc))
        simp only [last, Bool.false_eq_true, ↓reduceIte, ite_self] at scan
        simpa [v₀] using scan
      · simpa [v₀, compValues, width] using scan
    exact scan'.halt (comp_ret C e mode false f h B vs bs)


/-- The inner cap is computed from the saved first-field separator: dividing its physical
position by four gives exactly `|x| + 1`. No bit of the inner payload is decoded.

**Proof sketch.** Copy the saved boundary and halve it twice. Instantiate the shared
polynomial routine with the inner coefficient and exponent at this exact base. -/
private lemma comp_inner_prepare (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (n : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ compBound C e h.length)
    (hb : v 4 = 4 * n + 4) (ht : v 6 = 0) (ha : v 7 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hn : n ≤ h.length) :
    CompReach C e mode f h (compBound C e h.length) (some .innerPrepare, v, none)
      (some .lengthBound, Function.update (Function.update v 8 (n + 1)) 7 (C * (n + 1) ^ e), none) := by
  let B := compBound C e h.length
  let vz := Function.update v 8 0
  let vc := Function.update v 8 (4*n+4)
  let vd := Function.update v 8 (2*n+2)
  let vp := Function.update v 8 (n+1)
  have bz : ∀ r, vz r ≤ B := register_update_le v 8 B 0 hv (Nat.zero_le _)
  have bound : 4*n+4 ≤ B := by simpa [hb] using hv 4
  have bc : ∀ r, vc r ≤ B := register_update_le v 8 B _ hv bound
  have bd : ∀ r, vd r ≤ B := register_update_le v 8 B _ hv (by omega)
  have bp : ∀ r, vp r ≤ B := register_update_le v 8 B _ hv (by omega)
  have cp : CompReach C e mode f h B (some (.copy 6 false), vz, none) (some (.innerHalf false), vc, none) := by
    simpa [vz, vc, compCopy, hb] using comp_copy_run C e mode f h B 6 vz bz (by simp [vz, compCopy])
  have power := comp_power_bound C e h.length (n+1) e false (by omega) (by omega)
  have pol := comp_poly_run C e mode false f h B vp bp
    (by simp [vp, ht]) (by simp [vp, ha]) (by simp [vp, hi]) (by simp [vp, hs])
    (by simp [vp]) (by simpa [vp] using power.1) (by simpa [vp] using power.2)
  apply AReach.step ⟨comp_preS C e mode h _, hv⟩
  simp only [astep_clr (show compARM C e mode .innerPrepare = _ from rfl)]
  apply cp.trans
  apply AReach.step ⟨comp_preS C e mode h _, bc⟩
  simp only [astep_half (show compARM C e mode (.innerHalf false) = _ from rfl), vc,
    Function.update_self, Function.update_idem]
  rw [show (4*n+4)/2 = 2*n+2 by omega]
  apply AReach.step ⟨comp_preS C e mode h _, bd⟩
  simpa [astep_half (show compARM C e mode (.innerHalf true) = _ from rfl), vd, vp, compFactor,
    show (2*n+2)/2 = n+1 by omega] using pol

/-- The two lookup segments use the received indexing loop at strides one and two. -/
private def compWalk (C e : ℕ) (suffix : Bool) (i : ℕ) : CompState C e :=
  if i = 0 then .walk suffix false else if suffix && (i == 1) then .walk suffix true else .seek suffix

/-- A virtual-prefix or physical-suffix seek is a direct shared-fragment instantiation.

**Proof sketch.** Invoke `indexedSeek_loop` with stride one or two and the selected segment
boundary. Its hit and miss endpoints are precisely the corresponding ARM states. -/
private lemma comp_seek_run (C e : ℕ) (mode suffix : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B count : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hl : v (if suffix then 3 else 11) = v 0 + compStride suffix * count)
    (hb : v 13 + count ≤ B) (hq : v 13 ≤ v 5) :
    if v 5 < v 13 + count then
      CompReach C e mode f h B (some (.seek suffix), v, none)
        (some (if suffix then .suffixHit else .prefixHit),
          Function.update (Function.update v 0 (v 0 + compStride suffix * (v 5 - v 13))) 13 (v 5), none)
    else
      CompReach C e mode f h B (some (.seek suffix), v, none)
        (some (if suffix then .answer false else .separator false),
          Function.update (Function.update v 0 (v (if suffix then 3 else 11))) 13 (v 13 + count), none) := by
  apply indexedSeek_loop (compARM C e mode) (compOracle f) h 0 (if suffix then 3 else 11) 13 5
    (by cases suffix <;> decide) (by decide) (by decide) (by cases suffix <;> decide)
    (by cases suffix <;> decide) (by decide)
    (.seek suffix) (.probe suffix) (.next suffix) (if suffix then .suffixHit else .prefixHit)
    (if suffix then .answer false else .separator false) (compWalk C e suffix) (compStride suffix) B
    (by cases suffix <;> decide) rfl rfl rfl
  · intro i hi
    cases suffix with
    | false =>
      have iz : i = 0 := by simp [compStride] at hi; omega
      subst i; rfl
    | true =>
      have iz : i = 0 ∨ i = 1 := by simp [compStride] at hi; omega
      rcases iz with rfl | rfl <;> rfl
  · cases suffix <;> rfl
  · exact hv
  · exact hl
  · exact hb
  · exact hq

/-- An oracle-return node returns exactly its answer, preserving every register. -/
private lemma comp_call_return (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (l : CompState C e) (j : Fin 4) (r : Fin 14)
    (hc : compARM C e mode l = .call j .whole [r] (.answer true) (.answer false)) :
    CompHalt C e mode f h B (some l, v, none) (compOracle f j (pairEncode h (Nat.bits (v r)))) := by
  apply AHalt.step ⟨comp_preS C e mode h _, hv⟩
  rw [astep_call hc, vword_whole₁]
  cases ans : compOracle f j (pairEncode h (Nat.bits (v r))) <;>
    simpa [ans] using comp_ret C e mode _ f h B v hv

/-- A matching suffix position accepts in length mode and reads the physical bit in bit mode. -/
private lemma comp_suffix_hit (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (h : List Bool) (B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B) :
    CompHalt C e mode f h B (some .suffixHit, v, none) (if mode then true else h.getD (v 0) false) := by
  cases mode with
  | false => simpa only [comp_bit] using comp_call_return C e false f h B v hv .suffixHit 0 0 rfl
  | true => exact AHalt.ret rfl ⟨comp_preS C e true h _, hv⟩

/-- A matching prefix position reads the lifted `f` bit after halving the virtual address. -/
private lemma comp_prefix_hit (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b : List Bool) (p B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p)) B (some .prefixHit, v, none)
      (if mode then true else (f x).getD (v 0 / 2) false) := by
  cases mode with
  | true => exact AHalt.ret rfl ⟨comp_preS C e true _ _, hv⟩
  | false =>
    let vn := Function.update v 0 (v 0 / 2)
    have bn : ∀ r, vn r ≤ B := register_update_le v 0 B _ hv ((Nat.div_le_self _ _).trans (hv 0))
    have next := comp_call_return C e false f (pairEncode (pairEncode x b) (Nat.bits p)) B vn bn .prefixBit 2 0 rfl
    have answer := comp_lifted f false x b p (vn 0)
    simp only [Bool.false_eq_true, ↓reduceIte] at answer
    rw [answer] at next
    apply AHalt.step ⟨comp_preS C e false _ _, hv⟩
    simpa [astep_half (show compARM C e false .prefixHit = _ from rfl), vn] using next


/-- A suffix lookup reads exactly the retained payload bit or rejects past its end.

**Proof sketch.** Invoke the shared indexed seek at physical stride two. Its hit address
is the proved nested-pair suffix address. A miss means the default bit and length answer
are both false. -/
private lemma comp_suffix_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b : List Bool) (p B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hp : v 0 = 4*x.length+4) (he : v 3 = 2*(pairEncode x b).length)
    (hi : v 13 = 2*(f x).length+2) (hq : v 5 = p)
    (le : 2*(f x).length+2 ≤ p) (total : 2*(f x).length+2+b.length ≤ B) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p)) B (some (.seek true), v, none)
      (if mode then decide (p < 2*(f x).length+2+b.length)
        else b.getD (p-(2*(f x).length+2)) false) := by
  let h := pairEncode (pairEncode x b) (Nat.bits p)
  let n := 2*(f x).length+2
  have endpos : v 3 = v 0 + 2*b.length := by rw [he, hp, length_pairEncode]; omega
  have seek := comp_seek_run C e mode true f h B b.length v hv
    (by simpa [compStride] using endpos) (by simpa [hi] using total) (by omega)
  by_cases inside : p < n + b.length
  · have cond : v 5 < v 13 + b.length := by simpa [hq, hi, n] using inside
    simp only [if_pos cond, ↓reduceIte] at seek
    let addr := 4*x.length+4+2*(p-n)
    let vh := Function.update (Function.update v 0 addr) 13 p
    have path : CompReach C e mode f h B (some (.seek true), v, none) (some .suffixHit, vh, none) := by
      simpa [vh, addr, hp, hi, hq, n, compStride] using seek
    have ab : addr ≤ B := by have := hv 3; dsimp [addr, n] at *; omega
    have bh : ∀ r, vh r ≤ B := register_update_le _ 13 B p (register_update_le v 0 B addr hv ab)
      (by simpa [hq] using hv 5)
    have bit : h.getD (vh 0) false = b.getD (p-n) false := by
      simpa [vh, addr, h] using comp_suffix_address x b (Nat.bits p) (p-n) (by omega)
    have hit := comp_suffix_hit C e mode f h B vh bh
    rw [bit] at hit
    have truth : decide (p < n+b.length) = true := decide_eq_true inside
    change CompHalt C e mode f h B (some (.seek true), v, none)
      (if mode then decide (p < n+b.length) else b.getD (p-n) false)
    rw [truth]
    exact path.halt hit
  · have cond : ¬ v 5 < v 13 + b.length := by simpa [hq, hi, n] using inside
    simp only [if_neg cond, ↓reduceIte] at seek
    let vf := Function.update (Function.update v 0 (v 3)) 13 (v 13+b.length)
    have bf : ∀ r, vf r ≤ B := register_update_le _ 13 B _
      (register_update_le v 0 B _ hv (hv 3)) (by simpa [hi] using total)
    have bit : b.getD (p-n) false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : b.length ≤ p-n)]
    have ans : (if mode then decide (p < n+b.length) else b.getD (p-n) false) = false := by
      simp only [inside, decide_false, bit, ite_self]
    rw [ans]
    exact seek.halt (comp_ret C e mode false f h B vf bf)

/-- Both separator cells and the following suffix have the exact paired-output semantics.

**Proof sketch.** Test the current output position, then the following position, returning
`false,true` for bit queries and accepting both for length queries. If neither matches,
advance past the separator and seek the retained suffix at its saved physical start. -/
private lemma comp_separator_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b : List Bool) (p B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (he : v 3 = 2*(pairEncode x b).length) (hb : v 4 = 4*x.length+4)
    (hi : v 13 = 2*(f x).length) (hq : v 5 = p) (le : 2*(f x).length ≤ p)
    (total : (pairEncode (f x) b).length ≤ B) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p)) B (some (.separator false), v, none)
      (if mode then decide (p < (pairEncode (f x) b).length) else (pairEncode (f x) b).getD p false) := by
  let h := pairEncode (pairEncode x b) (Nat.bits p)
  let n := 2*(f x).length
  have outlen : (pairEncode (f x) b).length = n+2+b.length := length_pairEncode _ _
  have firsteq : (if mode then decide (n < (pairEncode (f x) b).length)
      else (pairEncode (f x) b).getD n false) = mode := by
    have lt : n < (pairEncode (f x) b).length := by omega
    cases mode with
    | false =>
      change (pairEncode (f x) b).getD n false = false
      rw [pairEncode_getD, if_neg (by dsimp [n]; omega), if_pos rfl]
    | true => simp [lt]
  by_cases first : p = n
  · have eq : v 13 = v 5 := by omega
    have ans : (if mode then decide (p < (pairEncode (f x) b).length)
        else (pairEncode (f x) b).getD p false) = mode := by simpa only [first] using firsteq
    rw [ans]
    apply AHalt.step ⟨comp_preS C e mode h _, hv⟩
    simpa only [astep_jeq (show compARM C e mode (.separator false) = _ from rfl), if_pos eq] using
      comp_ret C e mode mode f h B v hv
  · have ne : v 13 ≠ v 5 := by omega
    let v₁ := Function.update v 13 (n+1)
    have b₁ : ∀ r, v₁ r ≤ B := register_update_le v 13 B _ hv (by omega)
    have headRun : CompReach C e mode f h B (some (.separator false), v, none)
        (some (.separator true), v₁, none) := by
      apply AReach.step ⟨comp_preS C e mode h _, hv⟩
      simp only [astep_jeq (show compARM C e mode (.separator false) = _ from rfl), if_neg ne]
      simpa only [astep_inc (show compARM C e mode (.separatorInc false) = _ from rfl), hi] using
        (AReach.single (A := compARM C e mode) (oracle := compOracle f) (x := h)
          (a := (some (.separatorInc false), v, none)) ⟨comp_preS C e mode h _, hv⟩)
    by_cases second : p = n+1
    · have eq : v₁ 13 = v₁ 5 := by simp [v₁, hq, second]
      have ans : (if mode then decide (p < (pairEncode (f x) b).length)
          else (pairEncode (f x) b).getD p false) = true := by
        have lt : p < (pairEncode (f x) b).length := by omega
        cases mode with
        | false =>
          change (pairEncode (f x) b).getD p false = true
          rw [pairEncode_getD, if_neg (by dsimp [n] at second; omega),
            if_neg (by dsimp [n] at second; omega), if_pos (by dsimp [n] at second; omega)]
        | true => simp [lt]
      rw [ans]
      apply headRun.halt
      apply AHalt.step ⟨comp_preS C e mode h _, b₁⟩
      simpa only [astep_jeq (show compARM C e mode (.separator true) = _ from rfl), if_pos eq] using
        comp_ret C e mode true f h B v₁ b₁
    · have beyond : n+2 ≤ p := by omega
      have ne₁ : v₁ 13 ≠ v₁ 5 := by simp [v₁, hq]; omega
      let v₂ := Function.update v 13 (n+2)
      let vz := Function.update v₂ 0 0
      let vs := Function.update v₂ 0 (v 4)
      have b₂ : ∀ r, v₂ r ≤ B := register_update_le v 13 B _ hv (by omega)
      have bz : ∀ r, vz r ≤ B := register_update_le v₂ 0 B 0 b₂ (Nat.zero_le _)
      have bs : ∀ r, vs r ≤ B := register_update_le v₂ 0 B _ b₂ (hv 4)
      have copy : CompReach C e mode f h B (some (.copy 7 false), vz, none) (some (.seek true), vs, none) := by
        simpa [vz, vs, v₂, compCopy] using comp_copy_run C e mode f h B 7 vz bz (by simp [vz, compCopy])
      have move : CompReach C e mode f h B (some (.separator true), v₁, none) (some (.seek true), vs, none) := by
        apply AReach.step ⟨comp_preS C e mode h _, b₁⟩
        simp only [astep_jeq (show compARM C e mode (.separator true) = _ from rfl), if_neg ne₁]
        apply AReach.step ⟨comp_preS C e mode h _, b₁⟩
        simp only [astep_inc (show compARM C e mode (.separatorInc true) = _ from rfl), v₁,
          Function.update_self, Function.update_idem]
        change CompReach C e mode f h B (some .suffixReset, v₂, none) _
        apply AReach.step ⟨comp_preS C e mode h _, b₂⟩
        exact copy
      have suffix := comp_suffix_run C e mode f x b p B vs bs (by simp [vs, hb])
        (by simp [vs, v₂, he]) (by simp [vs, v₂, n]) (by simp [vs, v₂, hq]) beyond
        (by simpa [outlen, n] using total)
      have bit : (pairEncode (f x) b).getD p false = b.getD (p-(n+2)) false := by
        rw [pairEncode_getD, if_neg (by dsimp [n] at beyond; omega),
          if_neg (by dsimp [n] at beyond; omega), if_neg (by dsimp [n] at beyond; omega)]
        congr 1
      simpa only [outlen, bit] using (headRun.trans move).halt suffix

/-- Lookup first seeks within the doubled virtual output of `f`, then delegates the two
separator cells and the retained suffix to their common continuation.

**Proof sketch.** The prefix seek is virtual stride one, so a hit is answered by the
lifted bit at half its index. A miss has index exactly twice the output length. This
includes an empty `f` output and flows into the proved separator/suffix continuation. -/
private lemma comp_lookup_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (x b : List Bool) (p B : ℕ) (v : Fin 14 → ℕ) (hv : ∀ r, v r ≤ B)
    (hp : v 0 = 0) (he : v 3 = 2*(pairEncode x b).length) (hb : v 4 = 4*x.length+4)
    (hf : v 11 = 2*(f x).length) (hi : v 13 = 0) (hq : v 5 = p)
    (total : (pairEncode (f x) b).length ≤ B) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p)) B (some (.seek false), v, none)
      (if mode then decide (p < (pairEncode (f x) b).length) else (pairEncode (f x) b).getD p false) := by
  let h := pairEncode (pairEncode x b) (Nat.bits p)
  let n := 2*(f x).length
  have nb : n ≤ B := by rw [length_pairEncode] at total; omega
  have seek := comp_seek_run C e mode false f h B n v hv
    (by simpa [hp, compStride, n] using hf) (by simpa [hi] using nb) (by simp [hi])
  by_cases inside : p < n
  · have cond : v 5 < v 13+n := by omega
    simp only [if_pos cond, Bool.false_eq_true, ↓reduceIte] at seek
    let vh := Function.update (Function.update v 0 p) 13 p
    have bh : ∀ r, vh r ≤ B := register_update_le _ 13 B p
      (register_update_le v 0 B p hv (by omega)) (by omega)
    have path : CompReach C e mode f h B (some (.seek false), v, none) (some .prefixHit, vh, none) := by
      simpa [vh, hp, hi, hq, compStride] using seek
    have ans : (if mode then true else (f x).getD (vh 0/2) false) =
        (if mode then decide (p < (pairEncode (f x) b).length) else (pairEncode (f x) b).getD p false) := by
      have lt : p < (pairEncode (f x) b).length := by rw [length_pairEncode]; dsimp [n] at inside; omega
      cases mode with
      | false =>
        change (f x).getD (p/2) false = (pairEncode (f x) b).getD p false
        rw [pairEncode_getD, if_pos inside]
      | true => simp [lt]
    rw [← ans]
    exact path.halt (comp_prefix_hit C e mode f x b p B vh bh)
  · have cond : ¬ v 5 < v 13+n := by omega
    simp only [if_neg cond, Bool.false_eq_true, ↓reduceIte] at seek
    let vm := Function.update (Function.update v 0 (v 11)) 13 n
    have bm : ∀ r, vm r ≤ B := register_update_le _ 13 B n (register_update_le v 0 B _ hv (hv 11)) nb
    have path : CompReach C e mode f h B (some (.seek false), v, none) (some (.separator false), vm, none) := by
      simpa [vm, hi] using seek
    exact path.halt (comp_separator_run C e mode f x b p B vm bm (by simp [vm, he])
      (by simp [vm, hb]) (by simp [vm, n]) (by simp [vm, hq]) (by omega) total)


/-- The canonicality predicate exactly matches the frozen reshaping definition. -/
private lemma compQ_field (f : List Bool → List Bool) (x b : List Bool) :
    compQ f (pairEncode x b) = if Canon b then pairEncode (f x) b else [] := by
  have canon : (Nat.bits (bitsVal b) = b) ↔ Canon b :=
    ⟨fun eq => eq ▸ canon_bits _, fun hc => (canon_eq_bits b hc).symm⟩
  simp only [compQ, pairDecode_pairEncode, canon]

/-- The two query languages share the program's mode bit. -/
private def compLang (f : List Bool → List Bool) (mode : Bool) : Language Bool :=
  indexLang fun z p => if mode then p < (compQ f z).length else (compQ f z).getD p false = true

/-- On a genuine outer query, the indicator is exactly the requested output bit or boundary test. -/
private lemma comp_lang_pair (f : List Bool → List Bool) (mode : Bool) (z : List Bool) (p : ℕ) :
    MultiTapeTM.indicator (compLang f mode : Set (List Bool)) (pairEncode z (Nat.bits p)) =
      if mode then decide (p < (compQ f z).length) else (compQ f z).getD p false := by
  rw [compLang, indicator_indexLang_pairEncode]
  cases mode <;> simp

/-- A word with no canonical paired representation is rejected in either mode. -/
private lemma comp_bad_query (f : List Bool → List Bool) (mode : Bool) (h : List Bool)
    (bad : ∀ z p, h ≠ pairEncode z (Nat.bits p)) :
    MultiTapeTM.indicator (compLang f mode : Set (List Bool)) h = false := by
  apply Bool.eq_false_iff.mpr
  intro accepts
  rw [indicator_eq_decide, decide_eq_true_eq] at accepts
  obtain ⟨z, p, eq, _⟩ := accepts
  exact bad z p eq

/-- Both outer-tail failure modes have false answers. Width rejection uses the full
composition bound; no unbounded numerical query is stored. -/
private lemma comp_rejected_tail {f : List Bool → List Bool} {C e : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length+1)^e) (mode : Bool) (z tail : List Bool)
    (bad : ¬ (Canon tail ∧ tail.length ≤ (Nat.bits ((2*C+3)*((pairEncode z tail).length+1)^(e+1))).length)) :
    MultiTapeTM.indicator (compLang f mode : Set (List Bool)) (pairEncode z tail) = false := by
  by_cases canonical : Canon tail
  · obtain ⟨p, rfl⟩ : ∃ p, tail = Nat.bits p := ⟨bitsVal tail, canon_eq_bits tail canonical⟩
    have wide : (Nat.bits ((2*C+3)*((pairEncode z (Nat.bits p)).length+1)^(e+1))).length <
        (Nat.bits p).length := Nat.lt_of_not_ge (fun width => bad ⟨canon_bits p, width⟩)
    have overflow := compQ_query_overflow hf z p wide
    rw [comp_lang_pair]
    cases mode with
    | false => exact overflow.1
    | true => simp only [↓reduceIte, overflow.2, decide_false]
  · apply comp_bad_query
    intro w p eq
    have fields := pairEncode_injective (a₁ := (z, tail)) (a₂ := (w, Nat.bits p)) eq
    have word : tail = Nat.bits p := congrArg Prod.snd fields
    exact canonical (word.symm ▸ canon_bits p)

/-- After valid inner syntax, compute the capped length and perform the output lookup.

**Proof sketch.** Compute the exact polynomial cap at `|x|+1`; the capped truthful search
returns `|f x|`, including equality with the cap and cap zero. The public fixed transfer
doubles this length into the virtual prefix boundary. Clear the pointer and use the
proved output-layout run. The full composition bound covers every output counter. -/
private lemma comp_valid_inner (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (bound : ∀ x, (f x).length ≤ C*(x.length+1)^e) (x b : List Bool) (p : ℕ)
    (canonical : Canon b) (v : Fin 14 → ℕ)
    (hv : ∀ r, v r ≤ compBound C e (pairEncode (pairEncode x b) (Nat.bits p)).length)
    (he : v 3 = 2*(pairEncode x b).length) (hb : v 4 = 4*x.length+4) (hq : v 5 = p)
    (ht : v 6 = 0) (ha : v 7 = 0) (hi : v 10 = 0) (hs : v 11 = 0)
    (hf : v 12 = 0) (hj : v 13 = 0) :
    CompHalt C e mode f (pairEncode (pairEncode x b) (Nat.bits p))
      (compBound C e (pairEncode (pairEncode x b) (Nat.bits p)).length)
      (some .innerPrepare, v, none)
      (if mode then decide (p < (pairEncode (f x) b).length) else (pairEncode (f x) b).getD p false) := by
  let h := pairEncode (pairEncode x b) (Nat.bits p)
  let B := compBound C e h.length
  have xn : x.length ≤ h.length := by simp only [h, length_pairEncode]; omega
  have room := comp_bound_room C e h.length
  have output : (pairEncode (f x) b).length ≤ B := by
    have cap := compQ_host_cap bound (pairEncode x b) (Nat.bits p)
    rw [compQ_field, if_pos canonical] at cap
    change (pairEncode (f x) b).length ≤ (2*C+3)*(h.length+1)^(e+1) at cap
    dsimp [B]
    omega
  have dbl : 2*(f x).length ≤ B := by rw [length_pairEncode] at output; omega
  let vp := Function.update (Function.update v 8 (x.length+1)) 7 (C*(x.length+1)^e)
  let vs := Function.update vp 12 (f x).length
  let vd := Function.update (Function.update vs 12 0) 11 (2*(f x).length)
  let vl := Function.update vd 0 0
  have powers := comp_power_bound C e h.length (x.length+1) e false (by omega) (by omega)
  have bp : ∀ r, vp r ≤ B := register_update_le _ 7 B _
    (register_update_le v 8 B _ hv (by omega)) (by simpa [compFactor] using powers.2)
  have bs : ∀ r, vs r ≤ B := register_update_le vp 12 B _ bp (by omega)
  have bd : ∀ r, vd r ≤ B := register_update_le _ 11 B _
    (register_update_le vs 12 B 0 bs (Nat.zero_le _)) dbl
  have bl : ∀ r, vl r ≤ B := register_update_le vd 0 B 0 bd (Nat.zero_le _)
  have polynomial := comp_inner_prepare C e mode f h x.length v hv hb ht ha hi hs xn
  have search := comp_length_search C e mode f h B (f x).length vp bp
    (by simp [vp, hf]) (by simpa [vp] using bound x)
    (by intro i _; simpa [h] using comp_lifted f true x b p i)
  have double : CompReach C e mode f h B (some .doubleTest, vs, none) (some .lookupReset, vd, none) := by
    have move := registerScale_loop (compARM C e mode) (compOracle f) h 12 11 (by decide)
      .doubleTest .doubleDown .lookupReset
      (fun i => if i = 0 then .doubleInc false else if i = 1 then .doubleInc true else .doubleTest)
      2 rfl rfl
      (by
        intro i hi
        have cases : i = 0 ∨ i = 1 := by omega
        rcases cases with rfl | rfl <;> rfl)
      rfl B vs bs (by simpa [vs, vp, hs] using dbl)
    simpa [vd, vs, vp, hs] using move
  have lookup := comp_lookup_run C e mode f x b p B vl bl (by simp [vl])
    (by simp [vl, vd, vs, vp, he]) (by simp [vl, vd, vs, vp, hb])
    (by simp [vl, vd]) (by simp [vl, vd, vs, vp, hj]) (by simp [vl, vd, vs, vp, hq]) output
  apply (polynomial.trans (search.trans double)).halt
  apply AHalt.step ⟨comp_preS C e mode h _, bd⟩
  exact lookup

/-- Inner shape and canonicality validation lead either to false or to the proved valid
inner computation. Arbitrary first fields and arbitrarily large canonical suffixes are
allowed.

**Proof sketch.** The received stride-two pair scan locates the inner suffix. A malformed
pair gives the empty reshaping. Save the suffix boundary and invoke the independent
last-bit canonicality check; its failure also gives the empty reshaping. Otherwise all
scratch is still clear, so the valid-inner computation applies. -/
private lemma comp_inner_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (bound : ∀ x, (f x).length ≤ C*(x.length+1)^e) (z : List Bool) (p : ℕ)
    (pb : p ≤ compBound C e (pairEncode z (Nat.bits p)).length) :
    CompHalt C e mode f (pairEncode z (Nat.bits p)) (compBound C e (pairEncode z (Nat.bits p)).length)
      (some (.scan true), compValues (pairEncode z (Nat.bits p)).length
        (tail := 2*z.length+2) (stop := 2*z.length) (query := p)
        (base := (pairEncode z (Nat.bits p)).length+1), none)
      (if mode then decide (p < (compQ f z).length) else (compQ f z).getD p false) := by
  let h := pairEncode z (Nat.bits p)
  let B := compBound C e h.length
  let v := compValues h.length (tail := 2*z.length+2) (stop := 2*z.length) (query := p) (base := h.length+1)
  change p ≤ B at pb
  have room := (comp_bound_room C e h.length).1
  have len : h.length = 2*z.length+2+(Nat.bits p).length := length_pairEncode _ _
  have bv : ∀ r, v r ≤ B := by simp [v, compValues, Fin.forall_fin_succ]; dsimp [B] at *; omega
  have scan := comp_pair_run C e mode true f h z B v bv (by simp [v, compLimit, compStride])
    (by intro i hi; simpa [v, compStride] using drop_first_read z (Nat.bits p) i hi)
  cases shape : pairDecode z with
  | none =>
    simp only [shape] at scan
    obtain ⟨t, tl, path⟩ := scan
    have bp : v 0 + compStride true*t ≤ B := by simp [v, compStride]; dsimp [B] at *; omega
    have out : compQ f z = [] := by simp [compQ, shape]
    simp only [out, List.length_nil, Nat.not_lt_zero, decide_false, List.getD_nil, ite_self]
    exact path.halt (comp_ret C e mode false f h B _ (register_update_le v 0 B _ bv bp))
  | some pair =>
    rcases pair with ⟨x, b⟩
    have eq := eq_pairEncode_of_pairDecode z x b shape
    subst z
    simp only [pairDecode_pairEncode] at scan
    let va := Function.update v 0 (4*x.length+4)
    let vb := Function.update va 4 (4*x.length+4)
    have addr : 4*x.length+4 ≤ B := by
      have vl : 2*(pairEncode x b).length ≤ B := by simpa [v] using bv 3
      rw [length_pairEncode] at vl
      omega
    have ba : ∀ r, va r ≤ B := register_update_le v 0 B _ bv addr
    have bb : ∀ r, vb r ≤ B := register_update_le va 4 B _ ba addr
    have scanned : CompReach C e mode f h B (some (.scan true), v, none) (some (.copy 4 false), va, none) := by
      simpa [va, v, compStride, Nat.mul_add, ← Nat.mul_assoc] using scan
    have save : CompReach C e mode f h B (some (.copy 4 false), va, none) (some .canonical, vb, none) := by
      simpa [vb, va, compCopy] using comp_copy_run C e mode f h B 4 va ba (by simp [va, v, compCopy])
    obtain ⟨vc, bc, frame, canonical⟩ := comp_canonical_run C e mode f x b (Nat.bits p) B vb bb
      (by simp [vb, va, v]) (by simp [vb])
    by_cases canon : Canon b
    · simp only [if_pos canon] at canonical
      rw [compQ_field, if_pos canon]
      apply (scanned.trans (save.trans canonical)).halt
      apply comp_valid_inner C e mode f bound x b p canon vc bc
      all_goals first
        | (rw [frame _ (by decide)]; simp [vb, va, v])
    · simp only [if_neg canon] at canonical
      rw [compQ_field, if_neg canon]
      simp only [List.length_nil, Nat.not_lt_zero, decide_false, List.getD_nil, ite_self]
      exact (scanned.trans (save.trans canonical)).halt (comp_ret C e mode false f h B vc bc)


/-- The composition-query ARM halts correctly on every physical input within one fixed
polynomial register bound.

**Proof sketch.** Count the host and validate its outer pair. Save the pair boundaries,
construct the full output cap, and validate the canonical outer index before decoding.
Malformed or over-width queries reject by the proved language laws. The bounded decoded
query then enters the complete inner validation, capped search, and output-layout run. -/
private lemma comp_run (C e : ℕ) (mode : Bool) (f : List Bool → List Bool)
    (bound : ∀ x, (f x).length ≤ C*(x.length+1)^e) (h : List Bool) :
    CompHalt C e mode f h (compBound C e h.length) (some .count, fun _ => 0, none)
      (MultiTapeTM.indicator (compLang f mode : Set (List Bool)) h) := by
  have room := (comp_bound_room C e h.length).1
  have count := inputLength_loop (compARM C e mode) (compOracle f) h 1 1 .count .countInc (.scan false)
    rfl rfl (fun i _ => comp_len f h i) (compBound C e h.length) (by omega) (fun _ => 0)
    (by intro r; exact Nat.zero_le _) (Nat.zero_le _)
  have vec : Function.update (fun _ : Fin 14 => 0) 1 h.length = compValues h.length := by
    have zero : (fun _ : Fin 14 => 0) = compValues 0 := by
      simp only [compValues, Matrix.vec_single_eq_const, Matrix.vecCons_const]
    rw [zero]
    simp
  rw [vec] at count
  have bv : ∀ r, (compValues h.length) r ≤ compBound C e h.length := by
    simp [compValues, Fin.forall_fin_succ]; omega
  have scan := comp_pair_run C e mode false f h h (compBound C e h.length) (compValues h.length) bv
    (by simp [compLimit, compStride]) (by intro i _; simp [compStride])
  cases shape : pairDecode h with
  | none =>
    simp only [shape] at scan
    obtain ⟨t, ht, path⟩ := scan
    have bp : (compValues h.length) 0 + compStride false*t ≤ compBound C e h.length := by
      simp [compStride]; omega
    have answer := comp_bad_query f mode h (by
      intro z p eq
      rw [eq, pairDecode_pairEncode] at shape
      contradiction)
    rw [answer]
    exact (count.trans path).halt (comp_ret C e mode false f h (compBound C e h.length) _
      (register_update_le (compValues h.length) 0 _ _ bv bp))
  | some pair =>
    rcases pair with ⟨z, tail⟩
    have eq := eq_pairEncode_of_pairDecode h z tail shape
    subst h
    simp only [pairDecode_pairEncode] at scan
    have start : CompReach C e mode f (pairEncode z tail) (compBound C e (pairEncode z tail).length)
        (some .count, fun _ => 0, none)
        (some (.copy 0 false), compValues (pairEncode z tail).length (ptr := 2*z.length+2), none) := by
      apply count.trans
      simpa [compStride] using scan
    have prepare := comp_outer_prepare C e mode f z tail
    have decode := comp_outer_decode C e mode f z tail
    dsimp only at prepare decode
    by_cases good : Canon tail ∧ tail.length ≤
        (Nat.bits ((2*C+3)*((pairEncode z tail).length+1)^(e+1))).length
    · simp only [if_pos good] at decode
      obtain ⟨p, rfl⟩ : ∃ p, tail = Nat.bits p := ⟨bitsVal tail, canon_eq_bits tail good.1⟩
      have pb := query_index_bound p ((2*C+3)*((pairEncode z (Nat.bits p)).length+1)^(e+1)) good.2
      have bounded : p ≤ compBound C e (pairEncode z (Nat.bits p)).length :=
        pb.trans (comp_bound_room C e (pairEncode z (Nat.bits p)).length).2
      simp only [bitsVal_bits] at decode
      rw [comp_lang_pair]
      exact (start.trans (prepare.trans decode)).halt (comp_inner_run C e mode f bound z p bounded)
    · simp only [if_neg good] at decode
      rw [comp_rejected_tail bound mode z tail good]
      exact (start.trans prepare).halt decode

/-- Compile the single mode-parametrized construction against the four proved languages. -/
private lemma comp_mem {f : List Bool → List Bool} (hf : ImplicitlyLogspaceComputable f)
    (C e : ℕ) (bound : ∀ x, (f x).length ≤ C*(x.length+1)^e) (mode : Bool) :
    compLang f mode ∈ LOGSPACE := by
  apply arm_decides_poly (compARM C e mode) .count (compBank f) (compBank_mem hf)
    (8*(2*C+3)) (e+1)
  intro h
  exact comp_run C e mode f bound h

/-- **`comp`'s query reshaping is implicitly logspace computable** (phase P4.4b; proved): if `f` is, so is `compQ f`.

**Proof sketch.**

* **Bound.** `Complexity.compQ_length_le`.
* **The ARM.** Both query languages come from one abstract register machine with a mode bit
  over a four-oracle bank (`LogProg.arm_decides_poly`):
  * `inputBitLang` and `inputLenLang`;
  * `{z | dropIdx (dropIdx z) ∈ L}` for `L` each of `f`'s two query languages. These are in
    `L` by `Complexity.mem_LOGSPACE_preimage` twice along
    `Complexity.implicitlyLogspaceComputable_dropIdx`.

  A `whole` call on `[j]` from the host `h = ⟨w, bits p⟩` presents
  `⟨⟨w, bits p⟩, bits j⟩`, which two `dropIdx` turn into `⟨x, bits j⟩` (`dropIdx_pairEncode`).
* **The run** ([AB09, Lemma 4.17's proof]; the P4.4 audit's question-2 ledger):
  * (i) Validate `h`, with the overflow test before storing `p`.
  * (ii) Validate `w = ⟨x, b⟩` with `b` canonical: empty (the representation of `0`) or
    ending in `true`, using `LogProg.canon_eq_bits` and `LogProg.canon_bits`.
  * (iii) Find `F := |f x|` by lifted length queries at `j = 0, 1, …` while `j` is below the
    cap `C (|x| + 1)^e`. `F` is the first `j` whose query fails, or the cap itself when every
    query below it succeeds, since `|f x|` is at most the cap. A cap of `0` gives `F = 0`
    with no query.
  * (iv) Answer:
    * `p < 2F`: the lifted bit at `⌊p/2⌋`;
    * `p ∈ {2F, 2F + 1}`: the separator `[false, true]`;
    * otherwise: `b`'s bit at `p − 2F − 2`, read from `h` at its doubled position;
    * length: `p < 2F + 2 + |b|`. -/
theorem ImplicitlyLogspaceComputable.compQ {f : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) : ImplicitlyLogspaceComputable (compQ f) := by
  obtain ⟨C, e, bound⟩ := hf.1
  refine ⟨⟨2*C+3, e+1, compQ_length_le bound⟩, ?_, ?_⟩
  · simpa only [compLang, Bool.false_eq_true, ↓reduceIte] using comp_mem hf C e bound false
  · simpa only [compLang, ↓reduceIte] using comp_mem hf C e bound true

end Complexity
```
