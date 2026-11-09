# External audit pack — quantum E1 epoch boundary (fills of `Quantum/Basic`)

Campaign: quantum computation and complexity, plan `campaign/design/plans/QuantumComplexityPlan.md`.
Gate `quantum-phase1` (`campaign/gates/01-quantum-phase1/`) audited the P1 statements and closed
at commit `13c8664b`. Fill epoch E1 then proved all 52 sorried statements of
`TCSlib/Quantum/Basic/`. `workflow.md` §4 puts an audit round at every epoch boundary; **this pack
is that round for E1.**

**What this round audits.** It is not a re-audit of the statements, which round 2 of
`quantum-phase1` accepted and which the fill may not change. The proofs are machine-checked. This
round audits what a fill can get wrong despite compiling:
1. **The statement freeze.** No audited declaration was renamed, re-signed or restated, and the
   only changed bodies are the 52 that were `sorry`.
2. **The new public surface.** Six public declarations were added. Their statements, docstrings
   and placement are new trusted surface and need the same scrutiny the gate gave the originals.
3. **Debt.** Duplicated proved material, cumulatively, verified against the duplication ledger
   (audit template failure mode 5).
4. **Documentation fidelity.** Every nontrivial proof's sketch must describe the proof that is
   there (policy §3). Sixteen skeleton-time sketches were rewritten for this reason.
5. **Axioms.** Nothing in `Quantum` may depend on `sorryAx` any more, including the 19 definitions
   that inherited it through proof fields before E1 (gate round-1 note 9).

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization at a fill-epoch boundary. The
proofs are machine-checked — do not review tactic scripts for correctness. The failure modes you
are hunting are:

1. **Infidelity** — a new public definition or statement that does not mean what its docstring
   or cited source says.
2. **Trivialization** — a new statement satisfiable for degenerate reasons.
3. **Freeze violation** — any audited declaration whose statement changed, or any body change
   other than replacing a `sorry`. Verify with the attached diff, not only with the drift log.
4. **Stale documentation** — a proof sketch, module docstring or `## Main results` entry that no
   longer matches the code.
5. **Debt** — wholesale duplication of existing proved material. Report it at **major** with the
   proposed fix "human acknowledgment required". Verify the ledger (`campaign/fills/e1/REPORT.md`,
   § Duplication ledger) cumulatively: check that every pair the copy screen lists is classified
   correctly, and look for copies the screen could miss (the same fact proved twice by different
   text).

For **each of the 6 new public declarations**: restate it in your own words before reading its
docstring, compare against the docstring and any cited source, and argue in 2–5 sentences that it
is true as stated (its proof is machine-checked, so your argument checks that the statement says
what is intended). Do not give a blanket approval: an empty findings table must come with those
restatements.

## Scope

| Item | Where |
|---|---|
| Commit under audit | `a97fceca7c0f7b360f91cb08d4db5a5b33bdb548` on branch `quantum/e1-fill` of `Shilun-Allan-Li/tcslib` |
| Audited baseline (gate close) | `13c8664b44f2550a66a8fb2c94c73069614f072f` |
| Changed files | the 5 files of `TCSlib/Quantum/Basic/` (`Register`, `Gates`, `ApplyOn`, `Measure`, `Protocols`): 716 insertions, 106 deletions. No other TCSlib file changed |
| The change | `evidence/tcslib-e1.diff` (full `git diff` from the baseline, 1263 lines) and the five files at the commit under audit |
| Fill report | `campaign/fills/e1/REPORT.md`: verification, new public declarations, private helpers, duplication ledger, notes |
| Evidence | `campaign/fills/e1/evidence/logs/` and `scripts/`, all produced at the commit under audit |
| Prior rounds | `campaign/gates/01-quantum-phase1/resolutions.md` (statement gate, closed) |
| Standards | `policy.md`, `workflow.md` §3–4 |
| Sources | [dW26] arXiv:1907.09415 v6 §1.4, §2.1.2, App. A.4, if you want to check citations in new docstrings; optional |
| Out of scope | tactic proofs; the 33 counting-layer `sorry`s (epochs E2, E3); statements accepted by gate `quantum-phase1` |

## Repository-side attestations (MEASURED, `campaign/fills/e1/evidence/`)

- **Sweep (`logs/sweep.log`).** A fresh `scripts/lean_check_tree.sh` sweep of all 14 P1 modules at
  the commit under audit, in dependency order, never `lake build`:
  - all pass;
  - the 7 `Quantum` modules report **no diagnostic at all** (no `sorry`, no warning);
  - the total is 33 `sorry` warnings, all in `Complexity/Promise` and `Complexity/Counting`.
- **Axioms (`logs/axioms.log`, `scripts/Axioms.lean`).** 268 constants.
  - All **175** constants of the `Quantum` modules depend only on `propext`, `Classical.choice`
    and `Quot.sound`. This includes the 19 data definitions and the 18 equation lemmas that
    inherited `sorryAx` before E1, and `Ket.nonempty_reg_zero`.
  - The 33 `sorryAx` dependents are exactly the counting-layer statements.
- **Drift (`logs/drift.log`, `scripts/drift.py`).** Each declaration of the 10 non-facade P1 files
  is compared by name between the baseline and the commit under audit. Comments are stripped and
  whitespace normalized; both the signature and the full body are compared. 212 → 246
  declarations:
  - **0 removed;**
  - **0 signatures changed;**
  - **52 bodies changed**, which should be exactly the 52 former `sorry`s;
  - **34 added**, 6 public and 28 private;
  - 160 unchanged in signature and body.
- **Style.** `logs/style_lint.log`: `style_lint.py` reports 0 findings over the 14 files,
  including its "proof over ~20 lines has a sketch" check. `logs/campaign_style_lint.log`:
  `campaign_style_lint.py` reports 0 FAIL and 0 WARN over all 14. No line exceeds 100 characters
  (MAINTAINER).
- **Copy screen (`logs/copy_screen.log`, `scripts/copy_screen.sh`).** The repository's
  `scripts/copy-text-screen-v3.py` ran over the five E1 files plus `QuantumHamming.lean` and
  `QuantumSingleton.lean`: 130 declarations, 28 pairs. 21 pairs are among E1 files, each
  classified in the report; the other 7 are inside the two older files. No pair crosses between
  E1 and the older files.

## The new public declarations (6)

| Declaration | File | Statement (informal) |
|---|---|---|
| `inner_mulVec_of_mem_unitaryGroup` | `Register.lean` | for `U` unitary, `star (U a) ⬝ᵥ (U b) = star a ⬝ᵥ b` |
| `regAppendEquiv_symm_apply` | `Register.lean` | `(regAppendEquiv k m).symm y = (y ∘ castAdd m, y ∘ natAdd k)` |
| `inv_sqrt_two_mul_self` | `Gates.lean` | `(1/√2) · (1/√2) = 1/2` in `ℂ` |
| `applyOn_mulVec_apply` | `ApplyOn.lean` | `(applyOn w U *ᵥ v) y = ∑ᵤ U (y ∘ w) u · v (Function.extend w u y)` |
| `applyOn_wire_mulVec_apply` | `ApplyOn.lean` | `(applyOn (wire i) U *ᵥ v) y = ∑ₐ U (const (y i)) (const a) · v (update y i a)` |
| `applyOn_permMat_mulVec_apply` | `ApplyOn.lean` | `(applyOn w (permMat σ) *ᵥ v) y = v (Function.extend w (σ⁻¹ (y ∘ w)) y)` |

Three were private helpers that were promoted so that no other file had to copy them
(`regAppendEquiv_symm_apply`, `inv_sqrt_two_mul_self`, `inner_mulVec_of_mem_unitaryGroup`). The
three `applyOn_*_mulVec_apply` lemmas are general tools that Phase 2's circuits will need.
`Function.extend w u y` is Mathlib's "write `u` on the wires `w`, copy `y` elsewhere"; it is now
part of a public statement, so check that the docstrings explain it adequately.

## Specific questions for this round

1. **Freeze.** Read `evidence/tcslib-e1.diff`. Is every change to an audited declaration a
   replacement of `sorry` by a proof, or a docstring edit? Any other change is a finding.
   - The drift log claims the 52 changed bodies are exactly the former `sorry`s; spot-check
     several.
   - `Measure.lean` gained `open Matrix`. Confirm it changes no statement.
2. **New public declarations.** For each of the six:
   - Is the statement true and well-formed as stated?
   - Does the docstring say what it asserts?
   - Is it in the right file? (`inner_mulVec_of_mem_unitaryGroup` and `regAppendEquiv_symm_apply`
     are in `Register.lean`; `inv_sqrt_two_mul_self` is in `Gates.lean`.)
   - Is any of them a hidden duplicate of a Mathlib lemma that should be used instead?
   - `applyOn_wire_mulVec_apply` states the gate's entries at constant registers `fun _ => y i`.
     Is that the natural form for later use?
3. **Debt.** Check the duplication ledger against `logs/copy_screen.log`:
   - Do you agree that the 21 remaining pairs are tactic idiom across different statements, not
     copies of proved material?
   - Are the two removals real removals? `applyOn_mul` should now be derived from
     `applyOn_mulVec_apply`, and `permMat_mulVec_apply` from `applyOn_permMat_mulVec_apply`.
   - Is there duplication the screen cannot see, for example the same fact proved twice in
     different words?
4. **Sketches.** Policy §3 requires that a sketch describe the proof the code performs. Check the
   16 rewritten sketches (listed in the report's notes) against their proofs. Check also that the
   sketches the fill did *not* rewrite still match.
5. **Private helpers (28).** Is any of them a general fact that policy §1 (*Helpers*,
   *Construction reuse*) would want public in a shared location? Conversely, is any of the six
   promotions unnecessary?
6. **Process.** E1 was a single sequential fill owning all five files, not the parallel batches of
   `workflow.md` §4. Shared lemmas were therefore promoted in place, not requested for a later
   shared-file window. `superdense_decode`, which precedes `superdenseState_vec`, is proved from a
   private lemma placed before both, rather than by reordering audited declarations. Are these
   acceptable, or should they be recorded as deviations needing human acknowledgment?
7. **Anything else.** Any regression in documentation (module docstrings, `## Main results`) or
   anything the attestations misstate.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement or a freeze
violation; **major** = fixable but materially misleading as is, **or** accumulated debt (failure
mode 5) that the gate may not close over without explicit human acknowledgment; **minor** = edge
case, stale documentation, or naming/attribution defect; **note** = observation, no change
required.

## Attachments (the bundle)

One uploadable Markdown file, built by `evidence/make_bundle.sh`. It contains this pack verbatim,
then under `## ===== <path> =====` headers:
- the fill report;
- `campaign/gates/01-quantum-phase1/resolutions.md`;
- `policy.md` and `workflow.md`;
- `evidence/tcslib-e1.diff`;
- the five `Quantum/Basic` files at the commit under audit;
- every log and script under `campaign/fills/e1/evidence/`.

The bundle is not committed; its SHA-256 and section count go in this gate's `resolutions.md`.
