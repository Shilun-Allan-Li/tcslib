# Fill report — epoch E1 (`Quantum/Basic`)

Plan §5 orders the P1 fills as epoch E1 (the pure-math `Quantum/Basic` lemmas), then E2 (the
counting layer against an abstract model) and E3 (the polynomial-time closure facts). This report
covers E1. The audited baseline is the closing commit of gate `quantum-phase1`,
`13c8664b44f2550a66a8fb2c94c73069614f072f`.

| Item | Value |
|---|---|
| Branch | `quantum/e1-fill` (from `quantum/p1-basic`) |
| Final commit | `a97fceca7c0f7b360f91cb08d4db5a5b33bdb548` (fills through `f93c7ee6`, then the pre-audit cleanup below) |
| Files owned | `TCSlib/Quantum/Basic/{Register, Gates, ApplyOn, Measure, Protocols}.lean` |
| Targets | the 52 sorried statements in those files (10, 15, 11, 6, 10) |
| Result | **all 52 proved**; `TCSlib/Quantum/**` has no `sorry` left |
| Not in E1 | the 33 sorried statements of `Complexity/Promise` and `Complexity/Counting` (E2, E3), untouched |

## Verification (MEASURED, `evidence/logs/`, scripts in `evidence/scripts/`)

- **Sweep (`sweep.log`).** All 14 P1 modules pass `scripts/lean_check_tree.sh` in dependency
  order (direct `lean`, never `lake build`). The 7 `Quantum` modules report no warning or error.
  (The sweep counts `sorry` warnings and, separately, every other line containing `warning` or
  `error`; it does not count information messages.)
  The total is 33 `sorry` warnings, all in `Promise/Basic` (3), `Counting/PP` (2), `Counting/GapP`
  (15), `Counting/PolyTime` (8) and `Counting/Inclusions` (5).
- **Axioms (`axioms.log`).** A census of the 268 non-internal constants of the audited modules
  (names `Name.isInternal` does not flag; private declarations are internal and are covered
  through the public constants that use them, and by the sweep's `sorry` count). All 175
  constants of the `Quantum` modules depend only on `propext`, `Classical.choice` and
  `Quot.sound`. This includes the 19 definitions and the 19 theorems (18 equation lemmas and
  `Ket.nonempty_reg_zero`) that inherited `sorryAx` before E1 (gate note 9). The 33 `sorryAx`
  dependents are exactly the remaining counting-layer statements.
- **Statement freeze (`drift.log`, `drift.py`, comparing signatures and full bodies).** From 212
  declarations at the baseline to 246 (as counted by `drift.py`: 211 named declarations plus
  ApplyOn's anonymous `Decidable` instance, then 245 plus that instance; the anonymous `example`
  in `Measure.lean` was absorbed into `probQubit_zero_add_one`, see the errata):
  - **0 removed;**
  - **0 signatures changed;**
  - **52 bodies changed**, exactly the 52 filled statements;
  - **34 added** (below);
  - 160 unchanged in signature and body.
- **Style (`style_lint.log`, `campaign_style_lint.log`).** `style_lint.py` reports 0 findings
  over the 14 files. That includes its check that every proof over about 20 lines has a sketch,
  which caught one private helper during E1, now fixed. `campaign_style_lint.py` reports 0 FAIL
  and 0 WARN over all 14 (its per-file public count does not include ApplyOn's anonymous
  `Decidable` instance). No line exceeds 100 characters.

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

## Private helpers (28)

- **`Register.lean` (1).** `sum_norm_sq_eq_dotProduct`.
- **`Gates.lean` (4).** `reg1_cases`, `sum_reg1`, `toffoli_cnot_slice`, and `gate1_ext` (two
  one-qubit gates are equal if their four entries agree; shared by the five gate identities).
- **`ApplyOn.lean` (9).**
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

Screened mechanically with the repository's copy screen, `scripts/copy-text-screen-v3.py`
(`evidence/scripts/copy_screen.sh`, `evidence/logs/copy_screen.log`). It lists every pair of
like-kind declarations where one reproduces at least half of the other's body (at least 60
characters), over the five E1 files plus `ErrorCorrectingCodes/QuantumHamming.lean` and
`QuantumSingleton.lean`.

**Removed before this report.** The first screen also found real duplication from E1, now gone:
- `applyOn_mul` repeated the bijection argument of `applyOn_mulVec_apply` (465 characters). It is
  now derived from `applyOn_mulVec_apply`, which moved before it.
- `Protocols.lean`'s private `permMat_mulVec_apply` repeated the core of the public
  `applyOn_permMat_mulVec_apply` (73–76%). It is now derived from it at the identity embedding
  (`applyOn_refl`).
- Earlier, two near-copies (`(1/√2)² = 1/2`, and the inner-product/norm rewrite chain) were
  removed by promoting the shared fact to a public lemma, and the register-splitting lemma was
  promoted before any copy was made.

> **Superseded (E1 epoch audit).** The classification below is the fill's own, at `a97fceca`,
> and two of its rows were wrong: the `probQubit_zero_add_one` / `probQubit_basis` row was an
> anonymous `example` duplicating `probQubit_basis` (round 1, major 1), and the Hadamard rows hid
> the same square computed twice in `hadamardMat_mem_unitaryGroup` and `H_mul_H` (round 1,
> major 2). "Copies of proved material: none" was therefore false. Both duplicates are removed
> and acknowledged; the current ledger (15 E1 pairs, all idiom) is in
> `campaign/gates/02-quantum-e1/resolutions.md`, § Round-2 baseline. The counts below stay valid
> for `a97fceca`.

**Remaining pairs at the final commit: 21 among the E1 files** (the screen's other 7 pairs are
inside `QuantumHamming.lean` and `QuantumSingleton.lean`, which predate E1). None reproduces the
proof of the same fact. Each shares a tactic idiom across *different* statements:

| Pairs | What is shared | Classification |
|---|---|---|
| 12 among `X_mul_X`, `Z_mul_Z`, `S_mul_S`, `H_mul_H`, `H_mul_Z_mul_H` | `refine gate1_ext …; fin_cases a <;> fin_cases b <;> simp (config := …)`: the case split itself is already factored into the private `gate1_ext` | Idiom; five different gate identities |
| 3 pairs with `hadamardMat_mem_unitaryGroup` (with `gate1_ext`, `H_mul_H`) | the four-case split over `Reg 1` and the two-term sum | Idiom; it states unitarity of a matrix, not equality of gates, so it cannot use `gate1_ext` |
| 4 among `X_mulVec_apply`, `cnot_mulVec_apply`, `teleportState_vec_sum` | the rewrite chain `permMat_mulVec_apply, Function.Involutive.toPerm_symm, Function.Involutive.coe_toPerm` | Idiom; it reads three different permutation gates |
| `superdenseState_vec_aux` / `teleportState_vec` (62%) | the closing `fin_cases … <;> simp […] <;> ring_nf <;> rw [inv_sqrt_two_sq]` | Idiom; two different protocols |
| `probQubit_zero_add_one` / `probQubit_basis` (69 characters) | `rw [probQubit_eq …]` and a `simp` call | Idiom |

- **Copies of proved material: none.** (Superseded: see the note above.)
- **Unchanged from the gate:** the acknowledged overlap with Physlib (plan FD-1, FD-2) and with
  `QuantumHamming`'s `sigmaX`/`sigmaZ` (plan OQ-6). The screen finds no text shared between the
  E1 files and `QuantumHamming.lean`.

## Notes for the epoch-boundary audit

- **Sketches synchronized (policy §3).** Seventeen sketches written at skeleton time described
  routes the fills did not take. Before this report, each was rewritten to describe the proof that
  is there: `sum_norm_sq_mulVec_of_mem_unitaryGroup`; in `Gates.lean`, `permMat_mem_unitaryGroup`,
  `H_mul_H`, `X_mul_X`, `Z_mul_Z`, `S_mul_S`, `H_mul_Z_mul_H`, `Toffoli_apply_of_control_one`; in
  `ApplyOn.lean`, `applyOn_mul`, `applyOn_wire_X_mulVec_basis`,
  `applyOn_wires20_CNOT_mulVec_basis`; `probQubit_evolve_applyOnU_of_forall_ne`; in
  `Protocols.lean`, `teleportInit_vec`, `teleportState_vec`, `teleport_correct`,
  `superdense_decode`, `superdenseState_vec`. These are docstring changes only; the drift check
  strips comments.

- `Measure.lean` gained `open Matrix` (for the `*ᵥ` notation in a private helper). It changes no
  statement.
- The workflow's batch rules (`workflow.md` §4) assume several parallel fill agents with exclusive
  file ownership and zip delivery. E1 was one sequential fill owning all five files, so promoting
  a shared lemma happened in place, not through a "requested shared lemma" in a report. All six
  promotions are listed above, for the epoch audit to confirm.
- The proofs use only Mathlib and the audited statements. No TCSlib machine construction or host
  is involved (policy §1, *Hosts come first*).

## Errata (E1 epoch audit, round 1)

The epoch audit (`campaign/gates/02-quantum-e1/findings.md`) found the following errors in this
report; the text above is corrected in place, and the repairs to the Lean files are recorded in
`campaign/gates/02-quantum-e1/resolutions.md`.

- **Finding 8.** `ApplyOn.lean` has 9 private helpers, not 11 (the list was right; the total of 28
  was right). The 19 theorems that inherited `sorryAx` were 18 equation lemmas and
  `Ket.nonempty_reg_zero`, not 19 equation lemmas. The campaign lint's public count omits the
  anonymous instance. The sweep's second counter counts warning and error lines, not all
  diagnostics.
- **Finding 9.** The axiom census covers non-internal constants only. By kind, its 22 additions
  over the gate's census were 6 source theorems, 12 generated equation lemmas, 2 matchers and 2
  `congr_simp` lemmas, with no removals.
- **Round 2, findings R2-2 and R2-3.** The duplication ledger above is marked superseded, and
  the sketch count is 17, not 16 (the list was right).
- **Finding 1 and finding 7.** The final commit carried an anonymous `example` in `Measure.lean`
  restating `probQubit_basis` with the same proof. Neither `drift.py` nor the copy screen treats
  `example` as a command boundary, so both read it as part of `probQubit_zero_add_one`. The
  example is removed, and the round-1 evidence scripts recognize anonymous commands.
