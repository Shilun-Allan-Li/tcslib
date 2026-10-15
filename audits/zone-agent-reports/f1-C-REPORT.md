# ZF-C: alphabet target complete; one-tape continuation frontier

## Delivery status

**1 of 3 targets complete.** This uses the brief's expressly permitted
“alphabet target + frontier” delivery. It is **not** a completed ZF-C batch
or a request to close the three-target fill gate.

| Target | Status |
|---|---|
| `alphabet_reduction_spaceUsed` | Complete, including all-horizon trajectory containment and the audit's space ledger. |
| `one_work_tape_spaceUsed` | Unchanged baseline `sorry`; replacement witness remains to be constructed. |
| `one_work_tape_binary_spaceUsed` | Unchanged baseline `sorry`; fill only after the one-tape target is closed. |

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Source branch: `complexity/arora-barak-ch3-4`.
Working branch: `fill/zone-f1-C`.
**Recorded base:** `3e5dd8c7504725750720629a7be08855b89d4e87`.
Brief issue commit: `8f13d74ecba8e73a3642d605f462774092d7ef8a`.
The two owned sources are byte-identical between those two commits. The
checkout was never rebased, pushed, or submitted as a PR.

The attached brief and its repository copy were read, followed by all three
`zone-infra-*-findings.md` reports and `zone-infra-resolutions.md`.
The alphabet proof follows round 1's inherited route; the round-2/3
one-tape dispositions remain the binding continuation route.

## Completed proof

The witness is the existing `arTM (arCode) e M`. Its transition table,
configuration representations, correctness proof, and all existing
private declarations are unchanged.

1. `arSpacePhase` describes a boundary, read, write, or move configuration
   using the received representations. A physical transition either stays
   in its source cycle or completes that cycle; a halted boundary is fixed.
2. Induction over **physical** time gives a phase at every horizon.
   Every physical head position belongs to a **closed** block of a source
   position visited by source horizon `t + 1`. A leftward move can use the
   next source configuration's position. This is trajectory containment,
   including intermediate reads/writes/moves, not an endpoint argument.
3. A closed block has `W + 1` cells. When the source reaches a new cell,
   that block overlaps the preceding cell's block because the source head
   moves at unit speed. Hence its new contribution is at most `W`.
   Repeated source positions contribute nothing. Per tape this proves the
   sharper `W * spaceUsedByTape + 1` bound, including the read pass's extra
   boundary cell.
4. Summing gives the exact inherited ledger, for every physical horizon:

   ```text
   spaceUsed_arTM t ≤ W * spaceUsed_M (t + 1) + M.k.
   ```

   Apply `hS` to the same-length word `x.map e` at `t + 1`. Applying it at
   time zero also gives `M.k ≤ S x.length`, so the result is at most
   `(W + 1) * S x.length`.
5. The existing `arTM_computes` gives time `3 * W + 2` per source step.
   Choose that same coefficient for the target's time and space clauses.
   Zero tapes are covered by the empty sum. No monotonicity of `S` or `T`,
   input copying, eventual-halt hypothesis in the trajectory lemmas, or
   bound on a different input length is used.

The source horizon `t + 1` is deliberately a loose common horizon for all
physical visits through `t`; the hypothesis bounds **every** source
horizon. It is not a claim that one source step is simulated per physical
step. Time correctness separately uses the existing fixed-length cycle.

## New declarations

All ten additions are `private`; there are **no optional public exports**,
no new admitted helpers, and no new machine definition.

| Declaration | Role |
|---|---|
| `arSpacePhase` | Predicate relating a physical configuration to the four received representations for one source cycle. |
| `arSpacePhase_step` | Phase closure under a physical step, allowing exactly the source-step advance at cycle completion. |
| `arSpacePhase_run` | Phase invariant at every physical horizon, with source-cycle index at most that horizon. |
| `arMoveCfg_position` | A moving head belongs to the closed block of one of the source transition's endpoints. |
| `arTM_position_visited` | All-horizon trajectory containment in a closed block of a source-visited cell. |
| `arSpaceBlock` | Closed integer interval for one source cell and its read boundary. |
| `arSpaceBlock_card` | Closed-block cardinality. |
| `arSpaceBlock_inter` | Overlap of blocks whose source coordinates differ by at most one. |
| `arSpaceCover_card` | Width-times-source-cardinality plus one bound for a tape's whole block cover. |
| `arTM_spaceUsed` | Sum of the per-tape trajectory bounds for the received witness. |

The helper statements are generic where useful, but remain private under
this batch's ownership rule. A future shared-file window may promote the
closed-block trajectory/counting facts if another consumer needs them.

## Duplication ledger and freeze

**Ledger line — `Robustness/AlphabetReduction.lean`: 10 new private
declarations; 0 copied declarations / 0 copied lines introduced;
62 explicit declarations total (60 private), versus 52 (50 private) at
base. No copied-material family was identified in this file's base or
added material; cumulative identified copy count 0/62 = 0%.**

The proof cites the existing `arCfg`, `arReadCfg`, `arWriteCfg`,
`arMoveCfg`, `arReadCfg_zero`, `arReadCfg_step`, `arReadCfg_dispatch`,
`arWriteCfg_step`, `arWriteCfg_finish`, `arMoveCfg_step`,
`arMoveCfg_finish`, `arCfg_init`, `arCode`, and `arTM_computes`.
It uses the public `MultiTapeTM` run and unit-speed facts and Mathlib's
finite-set cardinality and `Finset.sum_nsmul` results. No existing
transition or representation proof is copied or generalized in place.

Borderline screen: `arSpaceCover_card` is new proof infrastructure for the
specific overlapping block cover. Its standard finite-set induction and
cardinality calculations are proved against public Mathlib lemmas.
It is not a copied `spaceUsedByTape_le_card_Icc` or §12 controller-space
family. No `Build/Zone` import or admitted Zone fact is used. The
phase predicate references the existing representations; it does not
redefine them. There are no undisclosed local copies of shared material.

**Reuse-not-copy sweep screen:** no sweep machinery is added, copied, or
modified in this partial delivery. The entire 1,045-line
`Robustness/SingleTape.lean` is byte-identical to base, including its
`SweepCell` family, `sweepTM`, audited theorems, regression warning, and
two Z4 holes. The received `sweepTM` is not used as a space witness.
This is a zero-copy delta, not a claim that the missing demand-grown
controller has been supplied.

The freeze check verifies:

- Entire alphabet prefix preceding its Z4 appendix is byte-identical.
- Alphabet target signature and docstring are byte-identical.
- Entire `SingleTape.lean` is byte-identical.
- Every new declaration is private; no audited declaration is removed.
- The git diff touches only `Robustness/AlphabetReduction.lean`.
- Both full owned sources are included in the archive, with the unchanged
  single-tape file supplied for context and continuation.

## Continuation frontier

There is no new counterexample to a target statement. The outstanding
work is the substantial new one-tape witness and its trajectory proof.
Do not close the remaining holes using the received `sweepTM`.

The inherited stationary-head regression remains in the unchanged
one-tape target's docstring: the source uses one visited work cell at all
horizons, while unconditional growth makes the received witness visit at
least `n + 3` cells on a length-`n` input. No fixed coefficient bounds this
by `2 * c` for every input length.

The following is a construction plan, **not a kernel-checked new witness**:

1. Retain the received `SweepCell`, `SweepAlphabet`, `sweepEmbed`,
   `sweepBoundary`, `sweepSymbol`, `blankRow`, `rightRow`, `headAt`,
   `tapeRow`, `tapeZone`, `readVisit`, and `writeVisit`. Cite
   `read_row`, `write_row`, `read_zone`, `write_zone`,
   `tapeZone_append`, and the length and blank-row facts.
2. Build genuinely new finite control that records boundary-head flags
   during the read sweep and computes whether the pending source action
   first crosses either boundary. Extend only a crossed boundary.
   The right extension can use the received `rightRow`; on the returning
   sweep, a newly required left block can be obtained from the existing
   blank-row/write transduction. Preserve the old controller unchanged.
3. Use the generic `Sweep.lean` zipper/transduction API:
   `sweepCfg`, `sweepRevCfg`, `sweep_run`, `sweep_run_reverse`,
   `sweep_generate`, and the one-cell movement lemmas. The existing
   local write/turn/stay zipper identities are also reusable. In contrast,
   `sweep_init`, `sweep_prepare`, `sweep_finish`, and `sweep_step` have
   the specific **old** `sweepTM` in their statements. They cannot simply
   be applied to the new witness; either establish a restricted transition
   agreement for a delegated phase or use the generic API. Copying those
   proof families is not an acceptable substitution.
4. Maintain a represented coordinate interval containing exactly the
   union of source-visited intervals, together with the boundary cells.
   Every source interval contains zero. Use that to bound the union by
   the sum of the per-tape cardinalities. Interleaving contributes the
   fixed factor `M.k`; physical boundaries contribute a constant. Prove
   containment for **every prefix of every phase**, with a crossing
   charged through the current source transition. Carry post-halt
   absorption explicitly.
5. For nonempty `Γ`, choose a total finite-control retraction of
   `SweepAlphabet Γ M.k` to `Γ` fixing `sweepEmbed`. Use it on native
   input reads, never by materializing an input copy. Relate arbitrary
   target input to its same-length retracted source input. The received
   `sweepInput` sends non-image symbols to `none`; that is not itself
   this total retraction. Correctness on mapped inputs alone does not
   discharge the target's all-target-input space quantifier.
6. Handle `M.k = 0` by citing `unusedTapeTM`, `unusedTapeCfg`,
   `unusedTape_step`, and `unusedTape_computes`, then prove the stationary
   unused head visits exactly one cell. For empty `Γ`, use the trivial
   one-tape machine that halts on its first transition; the model's
   initial state is live. All source input/output words are empty.
7. Bound each sweep by a constant times the source step index plus one,
   sum to the required quadratic time, and prove the common space
   coefficient. The old exact `sweepTime` formula is for unconditional
   growth and is not automatically a timing theorem for the new machine.
8. Only after the one-tape target is closed, fill the composite by the
   inherited coefficient `c₂ * (c₁ + 1)` for both time and space. Do not
   compare `S` at different lengths or add a monotonicity premise.

Any new controller-specific counterpart of old sweep material must be
screened again in the continuation ledger. This delivery adds no
controller stub and no partial composite proof depending on `sorryAx`.

## Verification

| Check | Result |
|---|---|
| `Robustness/AlphabetReduction` | Exit 0; fresh `.olean`; 0 errors, 0 sorry warnings. |
| `Robustness/SingleTape` | Exit 0; fresh `.olean`; 0 errors, exactly 2 unchanged target sorry warnings. |
| `Robustness/Oblivious` | Exit 0; fresh `.olean`; 0 errors, 0 sorry warnings. |
| `TuringMachine` facade | Exit 0; fresh `.olean`; 0 errors, 0 sorry warnings. |
| Full required import closure | 38/38 modules passed; 0 errors; 4 sorry warnings total. |
| Style lint | `style_lint: 0 FAIL, 11 WARN over 42 files`. |
| Freeze | All checks in `freeze.log` passed. |
| Bundle | `git bundle verify` passed. |

The four sweep admissions are exactly `CounterProgRun.lean:343`,
`SingleTape.lean:1014`, `SingleTape.lean:1036`, and `NDCodes.lean:187`.
Only the middle two are this batch's unfinished targets; the other two are
unchanged baseline admissions. The requested modules were checked in the
prescribed order, with their dependencies freshly compiled as needed.

All three target axiom prints, verbatim from `axioms.log`:

```text
'Turing.FinTM.alphabet_reduction_spaceUsed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.one_work_tape_spaceUsed' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinTM.one_work_tape_binary_spaceUsed' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Thus the alphabet target and its entire proof dependency closure are free
of `sorryAx`. The other two targets are explicitly **not closed**. The
brief's three-target zero-sorry/no-`sorryAx` gate has not been met; this is
the authorized alphabet-plus-frontier delivery.

Final sweep tail (complete output is `sweep.log`):

```text
Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
PASS TCSlib/Complexity/TuringMachine/Universal exit=0 seconds=26.19
CHECK TCSlib/Complexity/TuringMachine/NDCodes
TCSlib/Complexity/TuringMachine/NDCodes.lean:187:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/TuringMachine/NDCodes exit=0 seconds=2.57
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine exit=0 seconds=2.28
SWEEP PASS: all 38 modules freshly checked.
```

The checks use `scripts/lean_check_tree.sh`, with fresh output in
`.lake/tcslib-check-oleans`. No `lake build` was run, including indirectly
for cache setup. Only the required transitive imports and the four
requested final modules were checked; no unrelated repository build was
attempted.

Environment: Lean 4.25.0, compiler commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; Mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, as pinned in the repository.
Cached imports were fetched using the pinned cache hashes. The official
Lean kernel and libraries were unmodified. This runtime needed a
self-path compatibility adapter: its only rewrite maps a process's own
`/proc/<pid>/exe` lookup to `/proc/self/exe`. Its C source is included in
`verification/selfpath.c`; it changes no Lean proof checking.

The existing SingleTape size WARN is justified by the **“A-S2 spec layer
LANDED”** decision-log row in `AroraBarakChapters3-4Plan.md` (line 471 at
base), which reserves splitting for the D7 window. AlphabetReduction is
884 lines, below the 1,000-line warning threshold; file ownership and
private visibility require the new analysis to stay with the received
witness. No plan or shared file was modified.

## Integration

Delivery commit: `bc97e905ca3c1fcdfd4627498192a8b2f77b3803`.
One commit; only the alphabet source changes.
Patch: `patches/0001-Prove-all-horizon-space-bound-for-alphabet-reduction.patch`.
`git bundle verify` passed; its output is in `bundle-verify.log`.

Use the format-patch series with the recorded base, or fetch the bundle.
The bundle contains only this batch's commit range and declares its base
prerequisite. Verify `SHA256SUMS` before integration. The remaining two
Z4 admissions are intentional, unchanged continuation targets; their
axiom prints must not be mistaken for completed proofs.

Glossary: `W = Fintype.card Γ + 1` is the received fixed block width;
`c₁` and `c₂` are the continuation's first- and second-stage coefficients.
All other mathematical names are those of the existing source and brief.
