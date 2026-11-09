# Fill report — epoch E1 (`Quantum/Basic`)

Plan §5 orders the P1 fills as epoch E1 (the pure-math `Quantum/Basic` lemmas), then E2 (the
counting layer against an abstract model) and E3 (the polynomial-time closure facts). This report
covers E1. The audited baseline is the closing commit of gate `quantum-phase1`,
`13c8664b44f2550a66a8fb2c94c73069614f072f`.

| Item | Value |
|---|---|
| Branch | `quantum/e1-fill` (from `quantum/p1-basic`) |
| Final commit | `f93c7ee69a5c1f54e44436beed93f365e1423eae` |
| Files owned | `TCSlib/Quantum/Basic/{Register, Gates, ApplyOn, Measure, Protocols}.lean` |
| Targets | the 52 sorried statements in those files (10, 15, 11, 6, 10) |
| Result | **all 52 proved**; `TCSlib/Quantum/**` has no `sorry` left |
| Not in E1 | the 33 sorried statements of `Complexity/Promise` and `Complexity/Counting` (E2, E3), untouched |

## Verification (MEASURED, `evidence/logs/`, scripts in `evidence/scripts/`)

- **Sweep (`sweep.log`).** All 14 P1 modules pass `scripts/lean_check_tree.sh` in dependency
  order (direct `lean`, never `lake build`). The 7 `Quantum` modules report no diagnostics at all.
  The total is 33 `sorry` warnings, all in `Promise/Basic` (3), `Counting/PP` (2), `Counting/GapP`
  (15), `Counting/PolyTime` (8) and `Counting/Inclusions` (5).
- **Axioms (`axioms.log`).** 268 constants. All 175 constants of the `Quantum` modules depend
  only on `propext`, `Classical.choice` and `Quot.sound`. This includes the 19 definitions and 19
  equation lemmas that inherited `sorryAx` through proof fields before E1 (gate note 9). The 33
  `sorryAx` dependents are exactly the remaining counting-layer statements.
- **Statement freeze (`drift.log`, `drift.py`, comparing signatures and full bodies).** From 212
  declarations at the baseline to 245:
  - **0 removed;**
  - **0 signatures changed;**
  - **52 bodies changed**, exactly the 52 filled statements;
  - **33 added** (below);
  - 160 unchanged in signature and body.
- **Style (`style_lint.log`, `campaign_style_lint.log`).** `style_lint.py` reports 0 findings
  over the 14 files. That includes its check that every proof over about 20 lines has a sketch,
  which caught one private helper during E1, now fixed. `campaign_style_lint.py` reports 0 FAIL
  and 0 WARN over all 14. No line exceeds 100 characters.

## New public declarations (6) — for the epoch-boundary audit

No audited declaration was renamed, re-signed or restated. These public lemmas were added, each
with a statement-prose docstring, a proof sketch where nontrivial, and an entry in its module's
`## Main results`:

| Declaration | File | Why |
|---|---|---|
| `inner_mulVec_of_mem_unitaryGroup` | `Register.lean` | Unitaries preserve inner products. The audited `sum_norm_sq_mulVec_of_mem_unitaryGroup` is now proved from it, and the no-cloning proofs use it, so the rewrite chain exists once |
| `regAppendEquiv_symm_apply` | `Register.lean` | Splitting a register; first written as a private helper in `ApplyOn.lean`, promoted so `Protocols.lean` need not copy it |
| `inv_sqrt_two_mul_self` | `Gates.lean` | `(1/√2)² = 1/2`; first private, promoted so `Protocols.lean` need not reprove it |
| `applyOn_mulVec_apply` | `ApplyOn.lean` | A placed gate acting on an arbitrary vector, as a sum over the gate's own basis |
| `applyOn_wire_mulVec_apply` | `ApplyOn.lean` | The same for a one-wire gate, as a two-term sum |
| `applyOn_permMat_mulVec_apply` | `ApplyOn.lean` | A placed permutation gate relabels a vector's entries |

The last three are general tools. Teleportation and superdense coding are proved through them,
and Phase 2's circuits (plan Q2) will need them.

## Private helpers (27)

- **`Register.lean` (1).** `sum_norm_sq_eq_dotProduct`.
- **`Gates.lean` (3).** `reg1_cases`, `sum_reg1`, `toffoli_cnot_slice`.
- **`ApplyOn.lean` (11).**
  - the reconstruction of a register from its gate wires (`Function.extend`): `agreeOff_symm`,
    `agreeOff_trans`, `extend_comp`, `agreeOff_extend`, `extend_self`, `eq_of_agreeOff`;
  - `applyOn_mul_applyOn_of_disjoint`, `agreeOff_castAddEmb_iff`, `applyOn_permMat_mulVec_basis`.
- **`Measure.lean` (2).** `probQubit_eq_sum_norm_sq`, `applyOn_mulVec_proj`.
- **`Protocols.lean` (12).**
  - `inv_sqrt_two_sq` (derived from the public `inv_sqrt_two_mul_self`);
  - `cnot_extend_wires01`, `teleportState_vec_sum`, `permMat_mulVec_apply`, `flipAt_const`,
    `X_mulVec_apply`, `Z_mulVec_apply`, `X_pow_mul_self`, `Z_pow_mul_self`,
    `wire_sum_eq_mulVec`, `cnot_mulVec_apply`;
  - `superdenseState_vec_aux`: the audited `superdense_decode` precedes `superdenseState_vec`, so
    both are proved from this one lemma instead of reordering audited declarations.

## Duplication ledger

- **Copies of proved material: none.** Two near-copies made during E1 were removed before this
  report by promoting the shared fact to a public lemma: `(1/√2)² = 1/2`, and the
  inner-product/norm rewrite chain. The register-splitting lemma was promoted before any copy was
  made.
- **Similar technique, not copied (disclosed for the auditor's judgment).** `Protocols.lean`'s
  private `permMat_mulVec_apply` (`(permMat σ v) c = v (σ⁻¹ c)`) is proved by the same
  `Finset.sum_eq_single` step as the public `applyOn_permMat_mulVec_apply`. The statements
  differ: one is about an unplaced matrix, the other about a placed one. The unplaced form could
  later be derived from the placed one at the identity embedding.
- **Unchanged from the gate:** the acknowledged overlap with Physlib (plan FD-1, FD-2) and with
  `QuantumHamming`'s `sigmaX`/`sigmaZ` (plan OQ-6).

## Notes for the epoch-boundary audit

- `Measure.lean` gained `open Matrix` (for the `*ᵥ` notation in a private helper). It changes no
  statement.
- The workflow's batch rules (`workflow.md` §4) assume several parallel fill agents with exclusive
  file ownership and zip delivery. E1 was one sequential fill owning all five files, so promoting
  a shared lemma happened in place, not through a "requested shared lemma" in a report. All six
  promotions are listed above, for the epoch audit to confirm.
- The proofs use only Mathlib and the audited statements. No TCSlib machine construction or host
  is involved (policy §1, *Hosts come first*).
