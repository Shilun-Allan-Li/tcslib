# External audit pack — Phase 4 skeleton (uncomputability)

Audits commit `49d25a27` on `complexity/arora-barak-ch1`. Since the closed
phase-3 loop (`audits/phase3-resolutions.md`, gate commit `b61e876d`), exactly one
thing happened: the **phase-4 skeleton** landed — computability, `UC`, `HALT`,
Theorems 1.10-1.11, and the guarded-composition API that the phase-3 audit itself
mandated (round 2, finding 10 and Argument F). **No phase-1/2/3 `sorry` was filled
this round.** Record findings in `audits/phase4-findings.md`.

**Repository-side attestations** (verify or challenge, but they need not be redone
blind): a comment-stripped git comparison against gate commit `b61e876d` confirms
the changes to previously audited files are **purely additive** — every audited
line survives verbatim and in order; no declaration changed or was removed. All
modules elaborate with zero errors. `sorry` count 14 → 21: the 14 carried sorries
are textually unchanged, the 7 new ones are all phase-4.

## What changed / new surface

**New files (primary blind-restatement target):**

* `TCSlib/Complexity/Uncomputability/Computable.lean` —
  `Complexity.Computable` (def); `Turing.FinTM.Computes.exists_computesFunInTime`
  (sorry: a machine with no stated bound admits some bound).
* `TCSlib/Complexity/Uncomputability/Diagonalization.lean` —
  `Complexity.UC` (def, over an **arbitrary** `MachineCode`);
  `UC_eq_false_iff`, `UC_eq_true_iff` (proved); `UC_not_computable`
  (sorry — [AB09, Theorem 1.10]).
* `TCSlib/Complexity/Uncomputability/Halting.lean` —
  `Complexity.HALT` (def, totalized `false` off the pairing image);
  `HALT_eq_true_iff`, `HALT_pairEncode_eq_true_iff` (proved);
  `UC_computable_of_HALT_computable` (sorry — the reduction);
  `HALT_not_computable` (**proved** from the previous two — [AB09, Theorem 1.11]).

**Additions to previously audited files (flagged per standing practice — this is
audited surface changing, albeit additively):**

* `Finite.lean`: `Turing.FinTM.Computes` (def — computation with no time bound);
  `ComputesInTime.output_unique` (proved — determinism of completed outputs);
  `ComputesFunInTime.computes` (proved glue).
* `Composition.lean`: `computesFunInTime_ifEq` (sorry — fixed-string comparator);
  `exists_comp_partial` (sorry — **partial/guarded sequential composition**, the
  finding-10 obligation); `exists_cond` (sorry — branch on a decided predicate).
* `Encoding.lean`: `computesFunInTime_pairEncode_diag` (sorry — the diagonal
  pairing `α ↦ pairEncode α α` in linear time; the only code computation the
  reduction needs).

**New sorries (7):** `computesFunInTime_ifEq`, `exists_comp_partial`,
`exists_cond`, `computesFunInTime_pairEncode_diag`,
`Computes.exists_computesFunInTime`, `UC_not_computable`,
`UC_computable_of_HALT_computable`.

**Proved at skeleton time (Lean-checked — audit the *statements*):**
`ComputesInTime.output_unique`, `ComputesFunInTime.computes`, `UC_eq_false_iff`,
`UC_eq_true_iff`, `HALT_eq_true_iff`, `HALT_pairEncode_eq_true_iff`,
`HALT_not_computable`.

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions,
theorem statements, and remaining `sorry`s. Existing proofs are machine-checked —
do not review tactic scripts. Hunt: infidelity to the source, trivialization,
unprovable-as-stated sorries, and missing hypotheses. For every definition in
scope, restate it in your own mathematical English *before* reading its docstring,
then compare against the cited source and report daylight. For every sorry'd
theorem, argue in 2-5 sentences why it is true as literally stated, or exhibit the
problem. Do not give a blanket approval: an empty findings table must be justified
by the per-definition restatements. Priority order:

1. **Blind-restate the new declarations** against [AB09, §1.5-§1.5.1,
   Theorems 1.10-1.11] and, for the combinators, against your round-2 finding 10 /
   Argument F (attached): are `exists_comp_partial` and `exists_cond` the right
   rendering of "guarded simulation with buffered intermediate output"? They will
   be *built on*, so a wrong iff here is a blocker.
2. **Check the two proof sketches discharge entirely by stated results.** The
   design goal of this skeleton is that the fill for `UC_not_computable` and
   `UC_computable_of_HALT_computable` is assembly, not new mathematics: every step
   of each sketch names a stated declaration of this development. Verify no step
   silently needs something unstated (this is exactly the class of gap finding 10
   caught last round).
3. **Statement-level scrutiny of the generalizations**: Theorem 1.10 over an
   *arbitrary* `MachineCode` (see question 1); `HALT`'s totalization (question 2).
4. Assess the attestations in the header; attempt at least 3 adversarial
   instantiations (suggestions in question 7).

## Specific questions

1. `UC_not_computable` is claimed for **every** `MachineCode`, effective or not —
   effectivity enters only in Theorem 1.11. Your Argument F blueprint appears to
   use only `decode_encode`, the total-function normal form, and `exists_codeTM`.
   Challenge this: is there a degenerate (e.g. deliberately pathological,
   noncomputable-meaning) scheme for which `UC c` *is* computable, making the
   generalized statement false? Or does the diagonalization truly never need the
   scheme's effectivity?
2. `HALT` totalization: `false` off the image of `pairEncode` ("not a pair ⟹ does
   not halt"). [AB09] leaves the pairing convention implicit. Is this benign — does
   any step of the reduction, or any plausible downstream use, distinguish the
   off-image convention? Also: is `∃ output t, ComputesInTime` the right rendering
   of "halts" (vs. reaching the halting state — we claim these are equivalent since
   every halted configuration carries a finite output)?
3. `exists_comp_partial`: is the double-existential right-hand side
   (`∃ y, M₁ ↓ y ∧ M₂(y) ↓ w`) the correct guarded-composition contract? Walk the
   divergence cases (`M₁` diverges; `M₁` halts, `M₂` diverges on its output) and
   the uniqueness collapse of `y`. Could a machine `M` satisfy the iff vacuously in
   a way that defeats the reduction? The lemma is deliberately **untimed** —
   confirm no phase-4 use needs a timed version.
4. `exists_cond`: the predicate `p` is semantic and tied to `D` only through
   `hD : D.Computes fun x => [p x]` — is that the right interface? Is the
   input-head-rewind sketch sound from every head position, including on empty
   input? Note the register trick (a total decider with singleton output emits
   exactly one symbol per run — is that inference correct given append-only
   output?).
5. `Computes.exists_computesFunInTime`: the statement asserts only `∃ T` with no
   properties (no monotonicity, no constructibility). Is that strong enough for the
   diagonalization chain — `one_work_tape_binary` takes an arbitrary `T`? Any
   issue with the choice + `Finset.sup` sketch?
6. The unfolding lemmas: check orientations (`UC = false` ↔ accepts own code;
   `UC = true` ↔ negated existence) and the classical `if` renderings; check
   `HALT_pairEncode_eq_true_iff` really needs and correctly uses
   `pairEncode_injective` (a sorry'd statement — legitimate to build on, but flag
   if the dependence is heavier than stated).
7. Adversarial instantiations to attempt: a `MachineCode` with non-injective
   `encode` (we believe `decode_encode` forbids it — confirm); `α = []` and
   `x = []` through `UC`, `HALT`, and the reduction (`pairEncode [] []`); a
   constant `p` through `exists_cond`; `M₁ = M₂` self-composition through
   `exists_comp_partial`; the machine `D` that emits its bit *early* (long before
   halting) through the `exists_cond` register sketch; `w₀ = u = v = []` through
   `computesFunInTime_ifEq`.

## Known deviations (declared by the authors — verify they are benign)

* `UC` is scheme-parametric; Theorem 1.10 is stated for every `MachineCode`
  (the book fixes one representation). Effectivity appears only in Theorem 1.11.
* Acceptance is the completed singleton output `[true]`; `UC c α = true` covers
  divergence *and* every completed output other than `[true]` (your Argument F
  reading).
* `HALT` is totalized by `false` off the image of `pairEncode`; its pair format is
  the evaluator's code-first `pairEncode α x`.
* Theorem 1.11 is by reduction (as in the book), stated as its own lemma; the
  reduction's sketch uses only the **forward** clause of `Turing.universal`.
* The partial combinators are untimed (halting-relation level); time-bounded
  refinements are deferred until a result needs them.
* `Complexity.Computable` deliberately shares its name with Mathlib's
  `_root_.Computable` (namespaced; a bridge module will relate them later).

## Scope

| Item | Where |
|---|---|
| Files under audit | `TCSlib/Complexity/Uncomputability/{Computable,Diagonalization,Halting}.lean` (new); the additions in `TCSlib/Complexity/TuringMachine/{Finite,Composition,Encoding}.lean`; all 19 modules attached for context |
| Source text | Arora & Barak 2009, §1.5-§1.5.1 and Theorems 1.10-1.11 (PDF pp. 47-49), with §1.4-§1.4.1 (PDF pp. 45-47) for the interfaces consumed |
| Context | `AroraBarakChapter1Plan.md` (decision log), `policy.md`, `audits/phase3-reaudit-findings.md` (Argument F — the sketches cite it) |
| Out of scope | tactic scripts (Lean-checked); statements confirmed in closed rounds, beyond spot-checks; phase 5 (deferred indefinitely per the plan) |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
