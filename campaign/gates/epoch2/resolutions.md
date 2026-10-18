# Epoch 2 (fill round + merge refactor) — audit loop resolutions (CLOSED)

Protocol: `AroraBarakChapter1Plan.md` §5 "Fill campaign". External auditor:
cross-vendor LLM per decision log.

## Round 1 (`epoch2-pack.md` → `epoch2-findings.md`, audited at `ee32391c`)

**Zero mathematical blockers or majors.** All 26 new public `Simulation.lean`
declarations were blind-restated with no docstring mismatch; the refactor
surface (StateRenaming, the two `Finite.lean` promotions) was endorsed as
inspected with all 63 pre-existing public headers located unchanged; and all
three delivered constructions were certified against their audited designs —
the buffered layer with a complete boundary/tag case table and a fully
specified empty-input adversarial trace, the sweep controller with an
independently re-summed cost ledger (`S_k(t) = 2kt² + (5k+4)t + 2k + 2 ≤
(9k+6)(t+1)²`) and the neighbor-flag bookkeeping checked at both zone edges,
and the fold with exact crossing identities and the universal `foldSafe`
safety argument (case A14 discharged without the computation premise). The
auditor additionally ran ~63,000 bounded executable checks of the definitions
(positions/tags/moves, rewinds, appends, local sweep configurations, fold
movements, one-hot codes) — all passed — and re-tested the strengthened
verification gate with a stand-in compiler on all three failure conditions.
The statement freeze and the policy-lint results were independently
reproduced at source level.

Three minors, resolved in the closing commit:

| Finding | Resolution |
|---|---|
| 1 minor — `AlphabetReduction.lean`'s module "Deviations" paragraph still described the *sketch's* logarithmic block width, while the delivered `arCode` is one-hot width `|Γ| + 1` (correctly disclosed in the theorem appendix) | Module docstring now identifies the logarithmic width as the original sketch and cross-references the one-hot implementation note; theorem statement untouched (the wider fixed width only changes the existential constant) |
| 2 minor — the pack's attestation 4 claimed all new imports were `Mathlib.Data.Fintype.*`; the fills also added `Mathlib.Tactic.Ring`, `Mathlib.Tactic.DeriveFintype`, `Mathlib.Data.List.FinRange`, `Mathlib.Data.Sigma.Basic` (all precise; none a soundness concern) | Acknowledged; the shipped pack is preserved as the historical artifact (standing precedent). Future packs generate the import inventory programmatically (`git diff` on import lines), like the attachment inventory |
| 3 minor — `style_lint.py`'s declaration tally matched the docstring phrase "lemma advances" in `SingleTape.lean` (reported 3 public; the truth is 2) | The tally now runs on comment-stripped source (nesting-aware); re-run reproduces the auditor's corrected count. The lint's zero-FAIL claim remains scoped to its documented mechanical checks |

Note-level dispositions carried forward:

- **Epoch-3 merge promotions endorsed** (findings table + recommendations
  section): (1) C's optional-write normalization promoted at the **raw**
  configuration/action layer as `Action.apply_workTapes`-style, re-exported
  through Simulation; (2) B's `source_bounds` promoted (initialized-run only —
  no silent generalization to arbitrary starts); (3) B's generic sweep/zipper
  layer extracted to a **separate raw sweep module** rather than growing the
  896-line `Simulation.lean`; (4) `indexedVisit`/`indexedFold` promoted with
  the `Nodup` hypothesis preserved (the auditor exhibited why it is needed);
  (5) the unused-tape embedding optionally shared as a per-input **iff**.
  Controller-specific representations (`SweepState`, `sweepTM`, fold
  internals, the one-hot controller) stay private.
- **Epoch-3 design guidance** (finding 9, the remaining-admissions table):
  `universal`'s startup needs a **prefix-only extraction/canonization
  invariant preserving the unread suffix** — the final-output composition
  theorem alone does not give suffix-independent startup, so the evaluator is
  not discharged by `computesFunInTime_comp` plus a black box;
  `timed_universal` must count **source transitions** inside an explicit
  interpreter (a wall-clock cutoff on a black-box evaluator does not meet the
  statement); the canonizer construction may now cite the proved timed and
  guarded composition; `oblivious_of_mem_DTIME` needs its own trajectory
  argument (early source halts must not stop the physical schedule).
- **Axiom-conclusion phrasing** (finding 10): `UC_not_computable` is
  admission-free **for a supplied scheme** (`c : MachineCode` is a
  parameter); exhibiting a concrete effective scheme still runs through the
  admitted `exists_effectiveMachineCode`. Statements of campaign progress
  keep this distinction explicit.
- **Evidence distinctions** (findings 10, 11, attestation table): the round
  reproduced source-level facts (freeze, scans, lint, module order) and
  attested but did not re-execute elaboration/axioms; original delivery
  archives remain maintainer-held. Unchanged practice: raw logs and manifests
  are retained locally and can be attached if a later gate requires replay.

## Gate status

**CLOSED.** 17 of 21 audited sorries proved and audited; [AB09, Theorem 1.10]
fully machine-checked for every supplied scheme; the four remaining
admissions (`oblivious_of_mem_DTIME`, `exists_effectiveMachineCode`,
`universal`, `timed_universal`) retain audited sketches with the finding-9
implementation obligations recorded. Carried into epoch 3: the promotion
list above (merge pre-work), the prefix-only startup obligation in brief 3B,
the source-transition counter obligation in the epoch-4 brief, and the
programmatic import inventory for future packs.
