# External audit pack — quantum-phase1, round 2 (re-audit after repairs)

Campaign: quantum computation and complexity, plan `campaign/design/plans/QuantumComplexityPlan.md`,
statement phase **P1**: plan items Q1, Q0.1–Q0.6, Q0.9, and Q0.7's statements.

**Why there is a round 2.** Round 1 (`findings.md`, attached verbatim) reported 0 blockers,
2 majors, 6 minors and 3 notes. The gate rule (`workflow.md` §3) closes a gate only on a round with
zero blockers and zero majors, and a round with majors triggers repairs and a full re-audit. The
repairs and every disposition are in `resolutions.md` (attached).

**This round audits the whole P1 surface again, at the repaired commit.** It has three tasks:
1. **Verify each repair** against the round-1 finding it answers.
2. **Audit every new or changed declaration from scratch**: 18 new, 1 changed.
3. **Confirm the rest is unchanged.** For the 193 declarations the drift log shows unchanged, you
   may cite your round-1 restatements and arguments, but check the drift claim itself (task 3
   below). Report any regression.

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions, theorem
statements, and remaining `sorry`s. The proofs that exist are machine-checked — do not
review tactic scripts for correctness. The failure modes you are hunting are:

1. **Infidelity** — a definition that does not mean what the cited source means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons
   (vacuous hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Unprovability** — a `sorry`d statement that is false as stated, or whose stated
   form is subtly weaker/stronger than intended (boundary cases: empty input, `n = 0`
   qubits, `k = 0` gate wires, random strings of length `0`).
4. **Missing hypotheses** — especially finiteness, positivity, and well-formedness side
   conditions the informal source leaves implicit.
5. **Debt** — wholesale duplication of existing proved material, even when disclosed. Report it
   at **major** with the proposed fix "human acknowledgment required". Debt already
   acknowledged by the human maintainer (here: the Physlib design overlap and the
   `QuantumHamming` Pauli matrices, both recorded in the plan) is not re-reported unless its
   scope has grown.

For **every new or changed definition**: restate it in your own mathematical English *without
looking at the docstring first*, then compare against the cited source, and report any daylight.
For **every new or changed `sorry`d theorem**: argue in 2-5 sentences why it is true as literally
stated, or exhibit the problem. Attempt at least **3** new adversarial instantiations aimed at the
repairs. Do not give a blanket approval: your deliverable is the findings table, and an empty table
must come with the restatements and arguments that justify it.

## Scope

| Item | Where |
|---|---|
| Commit under audit | `4b2c72b3aea92bbe05cb3c2d1af9d1e51310e896` on branch `quantum/p1-basic` of `Shilun-Allan-Li/tcslib` |
| Round-1 commit | `d2d72d18ed5b5845ff25ae028490ee45600ae38f` |
| Lean files under audit (all lines) | the same 14 files as round 1 (table below) |
| Source texts | as in round 1: [Wat08] arXiv:0804.3401 v1 §II.1, §III.2, §IV.5; [dW26] arXiv:1907.09415 v6 §1.2–1.5, §2.1.2, App. A; **attach both PDFs**. Also [NC10] §2.3 and Box 12.1, [FR99] §2, [WZ82], [AB09] Def 17.6 |
| Prior round | `findings.md` (round 1, verbatim) and `resolutions.md` |
| Plan and standards | the plan (decision log rows of 2026-11-07; items Q0.10, Q0.11, Q1.7 added), `policy.md`, `workflow.md` §2–3 |
| Out of scope | tactic proofs; the received files `Randomized/Classes.lean`, `Randomized/PolyTimeModel.lean`, `ClassNP/NP.lean`, `ClassP/P.lean` (attached for reference); plan items outside P1 |

### Files under audit (MEASURED, `evidence-r2/logs/campaign_style_lint.log`, `evidence-r2/logs/sweep.log`)

| File | Lines | Public decls | `sorry` warnings | Changed since round 1 |
|---|---|---|---|---|
| `TCSlib/Quantum/Basic/Register.lean` | 258 | 29 | 10 | 5 new declarations |
| `TCSlib/Quantum/Basic/Gates.lean` | 329 | 48 | 15 | 3 new |
| `TCSlib/Quantum/Basic/ApplyOn.lean` | 226 | 21 | 11 | 4 new; one sketch corrected (finding 4) |
| `TCSlib/Quantum/Basic/Measure.lean` | 120 | 11 | 6 | none |
| `TCSlib/Quantum/Basic/Protocols.lean` | 262 | 25 | 10 | `no_cloning` changed, 3 new; module docstring (findings 1, 3) |
| `TCSlib/Quantum/Basic.lean` | 31 | 0 | 0 | none |
| `TCSlib/Quantum.lean` | 29 | 0 | 0 | imports every module (finding 7's follow-up) |
| `TCSlib/Complexity/Promise/Basic.lean`, `TCSlib/Complexity/Promise.lean` | 146, 23 | 13, 0 | 3, 0 | none |
| `TCSlib/Complexity/Counting/PP.lean` | 118 | 6 | 2 | docstrings only (finding 8) |
| `TCSlib/Complexity/Counting/GapP.lean` | 388 | 43 | 15 | 2 new; docstrings (findings 2, 5) |
| `TCSlib/Complexity/Counting/PolyTime.lean` | 141 | 10 | 8 | none |
| `TCSlib/Complexity/Counting/Inclusions.lean` | 98 | 5 | 5 | 1 new |
| `TCSlib/Complexity/Counting.lean` | 32 | 0 | 0 | none |

The "public decls" counts are the linter's, which counts named declarations. `ApplyOn.lean` also
declares one anonymous `Decidable (AgreeOff …)` instance, unchanged: 211 named declarations plus
that instance, 212 in all (round 1: 193 + 1).

## Repository-side attestations (round 2)

Marked **MEASURED** (log under `evidence-r2/logs/`, script under `evidence-r2/scripts/`) or
**MAINTAINER** (claim to verify).

- **Drift (MEASURED, `logs/drift.log`, `scripts/drift.py`).** Every declaration of the 10
  non-facade files at the two commits is compared, after stripping comments, by its signature
  (the text before its top-level `:=`, or the whole of a structure). 194 → 212 declarations:
  - **removed:** none;
  - **added:** 18, listed in the log;
  - **signature changed:** 1, `no_cloning` (finding 1);
  - **unchanged:** 193.

  The script compares signatures only. Docstring changes are listed in the next section, and
  `git diff d2d72d18 4b2c72b3 -- TCSlib` shows all of them (MAINTAINER: 8 files, 203 insertions,
  19 deletions).
- **Elaboration (MEASURED, `logs/sweep.log`).** A fresh `scripts/lean_check_tree.sh` sweep of the
  14 modules at the commit under audit, in dependency order, never `lake build`. All pass with no
  diagnostic other than `declaration uses 'sorry'`; the total is **85** (72 in round 1, plus 13
  new sorried statements).
- **Axiom census (MEASURED, `logs/axioms.log`, `scripts/Axioms.lean`).** 246 constants. No axiom
  occurs other than `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. The `sorryAx`
  dependencies are:
  - **85** theorems with their own `sorry`;
  - **19** theorems inheriting it: round 1's 18 `rfl` equation lemmas, plus
    `Ket.nonempty_reg_zero`, whose term proof uses `Ket.basis`;
  - **19** definitions inheriting it through proof fields only, unchanged from round 1 (your
    note 9).
- **Style (MEASURED).** `logs/style_lint.log`: `style_lint.py` reports 0 findings over the 14
  files. `logs/campaign_style_lint.log`: `campaign_style_lint.py`, run over the whole tree and
  filtered to the 14 audited files (`scripts/campaign_lint.sh`), covers **all 14** with 0 FAIL
  and 0 WARN. Round 1's log covered 11 (finding 7). The wider run then found the facade defect
  repaired in `4b2c72b3`.
- **Name screen (MEASURED, `logs/collision.log`).** No `Quantum`, `Counting`, `Promise` or
  `QuantumComplexity` namespace or declaration exists outside the audited files; a positive
  control finds them in the 10 audited files. As finding 11 notes, this is a name-collision
  check, **not** a semantic duplication check.
- **Numerical checks (MEASURED, `logs/numeric.log`).** 37 checks, 0 failures: the 27 of round 1,
  plus 10 for the new statements (`applyOn_wires20_CNOT_mulVec_basis` on all 8 inputs including
  `011 ↦ 111`; `applyOn_of_fin_zero` at `n = 0, 1, 3`; `X X = 1`, `Z Z = 1`, `X ≠ 1`;
  `superdenseState_vec` with its sign; `card_reg`; `gap_boolVerifier_int`; `abs_gap_le`). This is
  evidence, not proof.

## What changed (for tasks 1 and 2)

**Major 1 (`Protocols.lean`)**, three theorems in place of one:
- `no_cloning_of_overlap e ψ φ`. Hypotheses:
  `0 < ‖∑ x, star (ψ.vec x) * φ.vec x‖ < 1`. Conclusion: no unitary `U` and phases
  `‖c₁‖ = ‖c₂‖ = 1` with `U (ψ ⊗ e) = c₁ (ψ ⊗ ψ)` and `U (φ ⊗ e) = c₂ (φ ⊗ φ)`.
- `no_cloning e` (changed signature), under `[Nontrivial d]`: no unitary such that every `ψ` has
  a phase `c` with `U (ψ ⊗ e) = c (ψ ⊗ ψ)`.
- `no_exact_cloning e` (new name for the old statement), **without** `Nontrivial`: no unitary
  with `U (ψ ⊗ e) = ψ ⊗ ψ` exactly for every `ψ`.

**Major 2 (`GapP.lean`).** The module docstring's second sentence is replaced by the
scaled-numerator account of how quantum acceptance probabilities meet gap functions.

**Minors 3, 4, 5, 8** are docstring repairs:
- the `Protocols` divergence on message labels;
- the `applyOn_commute_of_disjoint` sketch;
- the `coinFill` docstring;
- the `PP.lean` citation of [AB09, Def 17.6] and the tie convention.

**Sanity statements**, all sorried with sketches, except as noted:
- `qubitEquivBool_zero` and `qubitEquivBool_one`, proved by `decide` in the skeleton (declared);
- `card_reg`, `Ket.isEmpty_of_isEmpty`;
- `Ket.nonempty_reg_zero`, proved by a term in the skeleton: `⟨basis Fin.elim0⟩`;
- `X_mul_X`, `Z_mul_Z`, `X_ne_one`;
- `applyOn_of_fin_zero`;
- `wires20`, a definition whose injectivity is proved `by decide`, with `wires20_apply`
  (by `rfl`) and `applyOn_wires20_CNOT_mulVec_basis`;
- `gap_boolVerifier_int`, `abs_gap_le`;
- `superdenseState_vec`;
- `inPP_polyTimeModel_headD`.

**Facade.** `TCSlib/Quantum.lean` now imports `TCSlib.Quantum.Basic.{Register, Gates, ApplyOn,
Measure, Protocols}` as well as `TCSlib.Quantum.Basic`, following `TCSlib/Programs.lean`.

## Errata to the round-1 pack (shipped packs are not edited)

- **Finding 6.** The suggested instantiation "`Eff ≡ False`: confirm each closure hypothesis
  holds" was wrong. The five closure implications hold vacuously, `HasConstVerifiers` fails, and
  no `PP` or GapP witness exists.
- **Finding 7.** The campaign-lint log covered 11 files, not 14. The declaration count was 193
  named declarations plus one anonymous instance.

## Specific questions for round 2

1. **No-cloning.**
   - Are the three statements true as literally stated?
   - Is `no_cloning_of_overlap`'s overlap `∑ₓ conj(ψ x) φ x` the inner product `⟨ψ, φ⟩` in the
     convention of [dW26, App. A]? `star` on `ℂ` is conjugation.
   - Is `no_cloning` now the physical statement you asked for in finding 1?
   - Is dropping `Nontrivial` from `no_exact_cloning` correct, including on a one-element basis?
2. **GapP's module docstring.** Is the scaled-numerator account now accurate, and specific enough
   that the later `BQP ⊆ PP` work (plan Q4.5) cannot read it as the false raw-entry claim?
3. **Drift.** Check `logs/drift.log`: that no round-1 declaration changed signature other than
   `no_cloning`, and that the round-1 declarations you restated still read as you restated them.
   The diff is small enough to read in full.
4. **New sanity statements.** Are they true as stated, and do they test what you intended in
   your proposals?
   - `applyOn_of_fin_zero` uses `U Fin.elim0 Fin.elim0` for the single entry of a `1 × 1`
     matrix over `Reg 0`.
   - `applyOn_wires20_CNOT_mulVec_basis` encodes your instance A05.
   - `inPP_polyTimeModel_headD` uses the set `{x | x.headD false = true}` as a `Language Bool`.
5. **Deferrals.** Are the deferred proposals acceptable as plan items Q0.10, Q0.11 and Q1.7, or
   should any of them hold this gate? The deferred proposals are the GapP bridge, the [AB09] tie
   variant, entangled-input teleportation, the empty-seed regression lemmas, and product-basis
   factorization.
6. **Facade.** Is importing every module from the area facade, as `TCSlib/Programs.lean` does,
   the right repair of what the full-coverage lint found?
7. **Anything else.** Any regression, and anything round 1 missed.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = statement is fixable but materially misleading as is, **or** accumulated
debt (failure mode 5) that the gate may not close over without explicit human
acknowledgment; **minor** = edge case or naming/attribution defect; **note** =
observation, no change required.

## Attachments (the bundle)

One uploadable Markdown file, built by `evidence-r2/scripts/make_bundle_r2.sh`. It contains this
pack verbatim, then each attachment under a `## ===== <path> =====` header:
- `findings.md` (round 1) and `resolutions.md`;
- `policy.md`, `workflow.md`, the plan;
- the 14 audited files and `TCSlib.lean`;
- the four received files;
- every file under `evidence-r2/`.

The bundle is not committed; its SHA-256 and section count go in `resolutions.md` when round 2
closes. Attach the [Wat08] and [dW26] PDFs separately.
