# Resolutions — quantum-phase1

The gate rule (`workflow.md` §3) is that a gate closes only on a round reporting zero blockers and
zero majors. Round 1 reported two majors, so this file records the repairs and opens round 2,
a full re-audit.

## Round 1

| Item | Value |
|---|---|
| Commit audited | `d2d72d18ed5b5845ff25ae028490ee45600ae38f` |
| Pack | `pack.md` (shipped; not edited since, errata below) |
| Bundle | not committed; SHA-256 `b63d50015cbed512f033671eb1a389e76c2dbc46b4cc9c265ca793ddff8ff11f`, 35 sections, built by `evidence/scripts/make_bundle.sh` |
| Auditor | an external model from a different vendor, in a fresh chat, with the bundle and the [Wat08] and [dW26] PDFs |
| Findings | `findings.md`, verbatim: **0 blockers, 2 majors, 6 minors, 3 notes**. No counterexample to any of the 72 sorried statements; per-statement arguments for all 72; 21 adversarial instantiations; answers to all 13 questions |

### Dispositions

| # | Severity | Finding | Disposition | Where |
|---|---|---|---|---|
| 1 | major | `no_cloning` demanded exact vector equality, which already fails for `ψ` and `-ψ`; presenting it as physical no-cloning was misleading | **Repaired.** Three theorems replace one. `no_cloning_of_overlap`: no unitary copies two states with overlap modulus strictly between `0` and `1`, a separate phase allowed on each copy (the auditor's preferred form). `no_cloning`: on a nontrivial basis, no unitary copies every state up to a state-dependent phase (the auditor's displayed statement). `no_exact_cloning`: the old exact-vector form, documented as a vector-level fact, with the unneeded `Nontrivial` hypothesis dropped (answer 5). The module's divergence claiming "the statement is the same" is removed | `Protocols.lean` |
| 2 | major | `GapP.lean` claimed each quantum gate entry is a gap function; gap functions are integer-valued, and `1/√2`, `i` are not integers | **Repaired.** The module docstring now says the bridge goes through scaled integer numerators: with `h` Hadamards, amplitudes are `(1/√2)^h` times sums of terms in `{±1, ±i}`, and the acceptance probability is `F(x)/2^h` for an integer `F` from the real and imaginary parts, with the denominator stated explicitly. The plan's FD-10 already said this and needed no change | `GapP.lean` |
| 3 | minor | `denseCode`'s message labels differ from [NC10, §2.3] without a notice | **Repaired.** Divergence added: `01` and `10` are interchanged relative to [NC10], and `X Z = -iY` differs from [NC10]'s `iY` by a global sign. The code is unchanged (the auditor agreed it is internally consistent) | `Protocols.lean` |
| 4 | minor | `applyOn_commute_of_disjoint`'s sketch gave the wrong intermediate register for one product order | **Repaired.** The sketch now names both intermediate registers, one per product order | `ApplyOn.lean` |
| 5 | minor | `coinFill`'s docstring stated the acceptance formula without its length condition and without the `false` default | **Repaired.** The docstring states the condition `m ≥ p |x| + 1` and the `false` default on short strings | `GapP.lean` |
| 6 | minor | The pack asked the auditor to confirm all six closure hypotheses hold for `Eff ≡ False`; `HasConstVerifiers` does not | **Pack erratum, acknowledged.** The correct expectation: the five closure implications hold vacuously, `HasConstVerifiers` fails, and no `PP` or GapP witness exists. No Lean change. Corrected in `pack-r2.md` | — |
| 7 | minor | The campaign-lint log covered 11 files, not 14, and the declaration count omitted the anonymous `Decidable` instance | **Pack erratum, acknowledged, and a real miss found.** Re-running `campaign_style_lint.py` over all 14 files (round-2 `evidence-r2/scripts/campaign_lint.sh`) reported that the area facade `TCSlib/Quantum.lean` did not import the modules under `Basic/`, as the rule (and the precedent `TCSlib/Programs.lean`) requires. **Repaired** in commit `4b2c72b3`. Round 1 had 193 named declarations plus one anonymous instance | `TCSlib/Quantum.lean` |
| 8 | minor | `PP` cited [AB09] at chapter level; [AB09, Def 17.6] assigns ties to members, `InPP` to non-members, unrecorded | **Repaired.** `InPP` and the module now cite [AB09, Def 17.6] and record the tie convention, the `f ± 1` shift that relates the conventions for polynomial time, and that no bridge theorem is claimed for arbitrary models. A bridge theorem becomes plan item Q0.11 | `PP.lean` |
| 9 | note | The 19 definitions inheriting `sorryAx` do so only through proof fields | **Accepted** as a statement skeleton, as the auditor recommends; the distinction between direct admissions, inherited theorems and inherited definitions is kept in every census (round 2: 85, 19 and 19) | — |
| 10 | note | `IsGapP polyTimeModel` has the standard GapP meaning, but no bridge theorem states it | **Deferred to plan item Q0.10**, as the auditor recommends (a counting predicate first) | plan §5 |
| 11 | note | No unacknowledged duplication; the namespace screen is not a semantic duplication check | **Accepted.** `pack-r2.md` no longer presents the collision screen as a duplication check | — |

### Sanity statements the auditor proposed (answer 13, § "Proposed machine checkable sanity statements")

| # | Proposal | Disposition |
|---|---|---|
| 1 | `qubitEquivBool` at `0` and `1`; `card (Reg n) = 2^n`; no ket on an empty basis; a ket on `Reg 0` | **Added:** `qubitEquivBool_zero`, `qubitEquivBool_one` (by `decide`), `card_reg`, `Ket.isEmpty_of_isEmpty`, `Ket.nonempty_reg_zero` |
| 2 | Zero-wire placement | **Added:** `applyOn_of_fin_zero` |
| 3 | `X ≠ 1`, `X X = 1`, `Z Z = 1`; a reversed, non-contiguous `CNOT` placement | **Added:** `X_ne_one`, `X_mul_X`, `Z_mul_Z`; `wires20` and `applyOn_wires20_CNOT_mulVec_basis` (the auditor's instance A05: `011 ↦ 111`) |
| 4 | Phase-permitting no-cloning | **Added** (finding 1) |
| 5 | Integer Boolean gap formula and `|gap| ≤ 2^m` | **Added:** `gap_boolVerifier_int`, `abs_gap_le` |
| 6 | Empty-seed equations and regression lemmas for the guards | **Not added.** Already covered: the guards are hypotheses of the statements, and the auditor's instances A11–A14 checked them. Can be added at fill time |
| 7 | Bridge to standard GapP | **Deferred:** plan item Q0.10 |
| 8 | A concrete polynomial-time `PP` language | **Added:** `inPP_polyTimeModel_headD` (first bit is `true`) |
| 9 | The [AB09] tie-convention variant | **Deferred:** plan item Q0.11 |
| 10 | Exact superdense state with its sign; factorization of product-basis probabilities | **Added:** `superdenseState_vec`. Factorization **not added**: no P1 statement uses it |

Also from the auditor's answer 4: teleportation with an input entangled with an outside system
becomes plan item Q1.7.

### Round-2 baseline

| Item | Value |
|---|---|
| Commit for round 2 | `4b2c72b3aea92bbe05cb3c2d1af9d1e51310e896` (repairs in `64ec6332`, the facade fix in `4b2c72b3`) |
| Drift from round 1 (`evidence-r2/logs/drift.log`) | 194 → 212 declarations: **0 removed, 18 added, 1 signature changed** (`no_cloning`, finding 1), 193 unchanged after comment stripping |
| Sweep | 14 modules pass; **85** `sorry` warnings (72 + 13 new statements), no other diagnostic |
| Axiom census | 246 constants: 85 theorems with their own `sorry`; 19 theorems inheriting `sorryAx` (the 18 of round 1 plus `Ket.nonempty_reg_zero`); 19 definitions inheriting it, unchanged; no axiom beyond `propext`, `Classical.choice`, `Quot.sound`, `sorryAx` |
| Lints | `style_lint.py`: 0 findings over 14 files. `campaign_style_lint.py`: 0 FAIL, 0 WARN over **all 14** files |
| Numerical checks | 37, 0 failures (27 from round 1 plus 10 for the new statements) |
| Pack | `pack-r2.md` |
