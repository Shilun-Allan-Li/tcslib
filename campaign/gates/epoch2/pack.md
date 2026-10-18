# External audit pack — Fill campaign, Epoch 2 (second fill round)

Audits commit `ee32391c` on `complexity/arora-barak-ch1`. Since the epoch-1
resolutions (`audits/epoch1-resolutions.md`), two things happened. **(a)** The
**epoch-2 merge refactor** (commit `24687122`, executing the epoch-1 audit's
endorsed pre-work): the new shared modules
`TuringMachine/StateRenaming.lean` (public `Action.mapState` moved verbatim
from `Oracle.lean`; new `Cfg.mapState` + application lemma;
`MultiTapeTM.relabelState` + step commutation + `relabelState_runFrom_init`)
and `TuringMachine/Simulation.lean` (the epoch-1 gadget layer, made public),
the two `Finite.lean` promotions (`computesInTime_iff`, generalized to any
alphabet, and `Computes.exists_computesInTime_iff`), and the rewiring of
`Encoding`/`Halting`/`Oracle`/`Composition` — with a declaration-level check
that no public name was lost. **(b)** The **epoch-2 fill round**: three
independent cloud agents (zip delivery — runners have no repository write
access) filled **all five epoch-2 targets**; the maintainer reviewed each
delivery against its brief and integrated the patches with authorship
preserved (five commits). **No audited statement changed at any point.**
Record findings in `audits/epoch2-findings.md`.

The campaign standing: **17 of the 21 audited sorries are now proved.** The
four that remain are `oblivious_of_mem_DTIME`, `exists_effectiveMachineCode`,
`universal`, and `timed_universal` — exactly epochs 3-4.

## Repository-side attestations (maintainer, local machine — verify or challenge)

1. **Statement freeze.** Net `git diff` from the pre-fill HEAD (`60bdab6b`)
   removes exactly 10 lines: the 5 target `sorry`s and 5 docstring closing
   lines, each re-appearing verbatim with an appended implementation note (the
   flagged appendix mechanism). Across the refactor (`9bb3176e → 24687122`),
   a declaration-name comparison shows no public declaration lost: 7 epoch-1
   private helpers were retired in favor of 6 public replacements plus the
   same-name promotions. All pre-existing declaration headers are unchanged;
   the three agent deliveries each shipped their own freeze evidence agreeing
   with this.
2. **Elaboration.** Full 24-module sweep via the strengthened
   `scripts/lean_check_tree.sh` (exit-status + fresh-olean enforcement; the
   epoch-1 finding-1 gate), fresh olean tree, Lean 4.25.0 / mathlib
   `029db123ddaa`: **zero `error:` lines, zero gate failures**, exactly 4
   `declaration uses 'sorry'` warnings (`Oblivious.lean:109`,
   `Encoding.lean:455`, `Universal.lean:102`, `Universal.lean:165`).
3. **Axiom footprints** (`#print axioms`, maintainer-run):

   ```text
   'Turing.FinTM.exists_comp_partial'        [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.computesFunInTime_comp'     [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.one_work_tape'              [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.nonnegative_heads'          [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.alphabet_reduction'         [propext, Classical.choice, Quot.sound]
   'Turing.FinTM.one_work_tape_binary'       [propext, Classical.choice, Quot.sound]
   'Complexity.UC_not_computable'            [propext, Classical.choice, Quot.sound]
   'Complexity.PAL_mem_P'                    [propext, Classical.choice, Quot.sound]
   'Complexity.mem_P_iff_one_work_tape'      [propext, Classical.choice, Quot.sound]
   'Turing.universal_quadratic'              [propext, sorryAx, Classical.choice, Quot.sound]
   'Complexity.UC_computable_of_HALT_computable' [propext, sorryAx, Classical.choice, Quot.sound]
   'Complexity.HALT_not_computable'          [propext, sorryAx, Classical.choice, Quot.sound]
   ```

   **[AB09, Theorem 1.10] (`UC_not_computable`) is now fully machine-checked
   with no admissions**, as are the complete normal-form chain and the P-level
   corollaries. The three remaining `sorryAx` carriers inherit it solely
   through `universal` (epoch 3B/4).
4. **Soundness scan.** No added `axiom`, `native_decide`, `implemented_by`,
   `extern`, or `unsafe` anywhere in the fills. One scoped elaboration option
   in `SingleTape.lean`: `set_option synthInstance.maxSize 8192 in` on a
   `DecidableEq` instance for the sweep controller's sum/sigma representation
   — a typeclass *search budget*, not a proof-checking bypass (the kernel
   still checks the result); the file-header options are unchanged.
   `derive_fintype%` (mathlib's deriving elaborator) is used for one `Fintype`
   instance. New imports across the fills: precise `Mathlib.Data.Fintype.*`
   modules only.
5. **Policy conformance** (new attestation; `scripts/style_lint.py`, added
   this round per the epoch-1 process discussion). Result over
   `TCSlib/Complexity`: zero FAIL in campaign files after fixing one genuine
   catch (the refactor's own `StateRenaming.lean` lacked a `## References`
   section — added); three FAILs remain in the pre-campaign legacy
   `NPReductions/*` files (missing References sections), **out of this
   branch's scope**, recorded for a separate cleanup; one WARN:
   `SingleTape.lean` at 1315 lines exceeds the policy 1000-line threshold —
   batch B **escalated this in its report** as a single cohesive construction
   (75 private helpers for one theorem), accepted for now with a possible
   later split if its zipper/transduction layer is promoted. Every `sorry`
   carries a sketch; facades import all children.
6. **Delivery provenance.** Three zip deliveries per the standardized epoch-2
   contents (report, sources, format-patch, git bundle, full sweep log under
   the strengthened gate, per-theorem axiom log, SHA256 manifest). Bases
   verified as `24687122`; sources, patches, and bundles mutually consistent;
   the agents' own sweep and axiom logs agree with the maintainer's
   independent runs. Agent reports preserved in `audits/epoch2-agent-reports/`.

## What was filled / new surface

| Batch | Now proved | New declarations |
|---|---|---|
| A (Composition + Simulation) | `exists_comp_partial`, `computesFunInTime_comp` (explicit `c = 2`) | **26 public** in `Simulation.lean` (the buffered-composition layer — the primary blind-restatement target): `tapeBlocks` + 3 projection lemmas, `bufferTape` + 4 lemmas + `bufferTape_append`, `VirtualTag`, `virtualMove`, `virtualNextTag`, `bufferTape_inputSymbol`, `virtualMove_correct`, `bufferedCompTM`, `bufferedFirstCfg` + `_init`/`_step`/`_run`, `bufferedSecondCfg` + `_step`/`_run`, `bufferedScanCfg` + `_run`, `bufferedFirstCfg_rewind`, `bufferedComp_start`. No new privates |
| B (SingleTape) | `one_work_tape` (constant `9k + 6`; separate `k = 0` lockstep path) | 75 private (zipper/transduction sweep machinery; inventory with line numbers in the batch-B report) |
| C (Bidirectional + AlphabetReduction) | `nonnegative_heads` (constant `1`), `alphabet_reduction` (constant `3L + 2`, one-hot width `L = card Γ + 1`) | 88 private (fold layer + block-code layer; inventory in the batch-C report) |

## Brief for the auditor

Ground rules as in all previous rounds (trusted surface; no blanket approval;
tactic scripts are Lean-checked and axiom-audited — out of scope). Priorities:

1. **Blind-restate the 26 new public `Simulation.lean` declarations** — they
   are shared audited surface that epochs 3-4 will build on. The semantic
   heart: does `VirtualTag`/`virtualMove`/`virtualNextTag` +
   `bufferTape_inputSymbol` + `virtualMove_correct` faithfully reproduce the
   clamped native input semantics (`Turing.moveInputPos`) on the buffer, for
   every word including the empty one?
2. **Spot-check the three delivered constructions against their audited
   sketches** (definitions, not tactics): `bufferedCompTM`'s three-block
   layout, live administrative states, and exact `|y| + 2` rewind ledger
   (phase-4 finding 3 and epoch-1 finding 11 dispositions); `sweepTM`'s
   tagged-payload alphabet `Γ ⊕ Option (Fin k × (Option Γ × Bool × Bool))` —
   verify a *marked blank* is representable and distinct from both the
   physical blank and the boundary (the phase-2 round-1 correction), the
   saved-neighbor-flag mechanism for single-pass head movement, and the
   closed-form `S_k(t) = 2kt² + (5k+4)t + 2k + 2 ≤ (9k+6)(t+1)²`;
   `foldTM`'s alphabet `Bool × Option Γ × Option Γ` (the phase-2 round-2
   correction), canonical blank packing (`foldPack`), stationary fold
   crossings, and the `foldSafe` layer establishing `NonnegativeHeads` on
   **every** input (case A14) — note the delivered constant is `1` with a
   single initialization step.
3. **`alphabet_reduction` deviations**: the one-hot code (width
   `card Γ + 1`) instead of the sketch's logarithmic width — confirm this is
   within the statement's existential constant and the docstring appendix
   says so honestly; the output decoder totalization off `e`'s image
   (`arEmission_in_image` via `output_prefix`).
4. **Confirm the four remaining sorries** match their audited forms and that
   their sketches remain implementable — in particular whether epoch 3's
   `exists_effectiveMachineCode` canonizer sketch can now cite the *proved*
   `computesFunInTime_comp`/`exists_comp_partial`, and whether `universal`'s
   sketch composes with the now-public buffered-simulation layer.
5. Assess attestations 1-6, including the scoped `synthInstance.maxSize`
   reasoning (attestation 4) and the policy-conformance dispositions
   (attestation 5).

## Specific questions

1. `VirtualTag` constrains only boundary positions and leaves interior tags
   free; `bufferedSecondCfg_run` threads the tag existentially. Is there any
   reachable configuration where an unconstrained interior tag could suppress
   a legitimate move (`virtualMove` fires only on a blank read — interior
   buffer cells are never blank; challenge this)?
2. `bufferedCompTM`'s phase-one action writes `(a.output.map some, if
   a.output = none then 0 else .pos)` on the buffer: confirm the buffer-head
   invariant (head = emitted length, at the right blank) survives the
   simulated *halting* transition emission, which `bufferedFirstCfg_step`
   claims to include.
3. B's controller records the *left-neighbor* head flag in each cell during
   the forward sweep and carries *right-neighbor* flags in control on the
   return sweep, enabling both movement directions in one return pass — is
   this bookkeeping sound at zone edges (fresh blocks written at both ends
   each macro-step), and does `source_bounds` justify the `[-t, t]` zone?
4. C's `nonnegative_heads` claims constant `1` (one initialization step, then
   one physical step per source step): verify `T n + 1 ≥ 1 + τ` covers the
   initialization accounting for every halting time `τ ≤ T n`, including
   `n = 0`, and that `foldSafe` really quantifies over arbitrary
   (non-embedded) inputs as `NonnegativeHeads` requires.
5. The three shared-lemma/promotion requests on file: C requests
   `arUpdated_tape` (optional-write normalization) for `Simulation.lean`; B
   lists candidates in its report. Which promotions do you endorse for the
   epoch-3 merge, and with what statements?
6. Adversarial instantiations: `M₁` emitting on its halting transition
   through `exists_comp_partial`; `y = []` and `x = []` through the buffered
   layer; `k = 0` through `one_work_tape` and `alphabet_reduction`; a source
   machine that never moves through `sweepTM` (zone stays `[0, 0]`?);
   `Γ = Bool` with `e = id` through `alphabet_reduction`; `T = 0`-valued
   bounds (note `not_computesInTime_zero` makes such hypotheses vacuous).

## Scope

| Item | Where |
|---|---|
| Files under audit | `Simulation.lean` (26 new public decls + module docstring addition), `Composition.lean` (two fills + appendices), `SingleTape.lean`, `Bidirectional.lean`, `AlphabetReduction.lean` (fills + private layers), `StateRenaming.lean` + `Finite.lean` (refactor surface, new since the last audited commit); all 24 modules attached |
| Source text | Arora & Barak 2009, §1.3 (Claims 1.5, 1.6, 1.8; PDF pp. 41-44) for the three simulations; §1.2 for the model |
| Context | `AroraBarakChapter1Plan.md`, `policy.md`, `audits/epoch1-{findings,resolutions}.md`, `audits/phase2-{findings,reaudit-findings}.md` (the corrected construction designs), briefs `briefs/epoch2-batch{A,B,C}.md`, agent reports `audits/epoch2-agent-reports/` |
| Out of scope | tactic proofs; statements confirmed in closed rounds beyond the freeze check; legacy `NPReductions/*` style findings (recorded, deferred) |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
