/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulations on related states

Two implementations of the same oracles may keep states of different types: in a security proof
the real game and its simulation often record different data for the same history (for BB1, the
committed identity with a group element `h`, or with an exponent `α_1`). If a relation `R`
between the two kinds of state holds at the start, and every call from related states gives
equal expectations to any two tests of the answer and the new state that agree at equal answers
and related states, then so does every simulated computation, for tests of the output and the
final state (`ProbComp.expect_simulate_rel`). This preserves equality of compatible test
expectations; it is not a coupling of the two runs supported on `R`. A coupling of each call's
outcomes supported on equal answers and related states gives the per-call hypothesis
(`ProbComp.expect_sample_rel` for one uniform sample), but for an arbitrary relation the
hypothesis does not make the final states coupled inside `R` (Gate 49, G49-01). In particular
the output laws agree (`ProbComp.prob_simulate_rel`).

With one state type and `R` the equality this is `ProbComp.expect_simulate_congr`
(`Games.Hopping`); with `R s t ↔ s = f t` it is the law form of `simulate_eq_of_abs`
(`Games.Simulate`), without a query budget.

## Main definitions

None.

## Main results

* `ProbComp.expect_simulate_rel`: implementations on related states simulate alike.
* `ProbComp.prob_simulate_rel`: events on the output have the same probability, so games that
  return a bit computed from the output have the same acceptance probability.
* `ProbComp.expect_sample_rel`: a call that draws one uniform sample meets the hypothesis of
  `expect_simulate_rel` when a bijection of the samples matches the answers and relates the new
  states.

## References

* [BGZ09] G. Barthe, B. Grégoire, S. Zanella Béguelin, *Formal Certification of Code-Based
  Cryptographic Proofs*, POPL 2009.
* [Sho04] V. Shoup, *Sequences of Games: A Tool for Taming Complexity in Security Proofs*,
  Cryptology ePrint Archive 2004/332, revision of 18 January 2006.
-/

namespace TCSlib.Cryptography.Games

namespace ProbComp

variable {ι : Type} {spec : OracleSpec ι} {σ τ α : Type}

/-- **Implementations on related states simulate alike.** Let `impl₀` keep states in `σ` and
`impl₁` in `τ`, related by `R : σ → τ → Prop`. Suppose that every call from related states
`R s t` gives the same expectation to any function `g₀` of the answer and the new `σ`-state and
any function `g₁` of the answer and the new `τ`-state that agree at equal answers and related
states:
`(∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) → 𝔼[g₀] (impl₀ i x s) = 𝔼[g₁] (impl₁ i x t)`.
Then from related states the simulations of every computation `c` do the same for functions of
the output and the final state: if `R s t`, and `G₀ (a, s') = G₁ (a, t')` whenever `R s' t'`,
then `𝔼[G₀] (simulate impl₀ c s) = 𝔼[G₁] (simulate impl₁ c t)`.

The conclusion has the form of [BGZ09, §4.1, lemma (=⟦⟧)]: runs from related states give equal
expectations to test functions that agree along the relation. The relation is carried as pre-
and postcondition of every call, as the invariant `φ` of [BGZ09, §4.2, ⊨_φ] (judgments in the
sense of [BGZ09, §4.1, Def. 5]). The computation `c` is an arbitrary context that reaches the
two implementations only through its oracle calls, like a well-formed adversary, which is free
to call oracles [BGZ09, §3.4]; [BGZ09, §5.2, Lemma 1] proves an equivalence inside an arbitrary
context, and §5.2 applies it to replace one oracle by another. A run of `c` against `impl₁` in
place of `impl₀` is a bridging step, `Pr[S_i] = Pr[S_{i+1}]` [Sho04, §1.1, bridging steps], as
in the replacement of a random function by a lazily tabulating oracle [Sho04, §4.2, Game 2].

**Deviation:** [BGZ09] states no rule for adversary calls with a relational invariant. This lemma
generalizes its `(=⟦⟧)` and `⊨_φ` (§4.1–§4.2) to oracle simulations whose states are related by
an invariant, in the arbitrary-context style of §5.2. The per-call hypothesis (equal
expectations of test functions that agree along `R`) is the library's formulation.

**Proof sketch.** Induction on `c`, generalizing the two states. At a return `a`, `R s t` gives
`G₀ (a, s) = G₁ (a, t)`. At a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`); by the induction hypothesis the two
continuation values agree at equal answers and related new states, so the hypothesis on the call
equates them. -/
theorem expect_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (G₀ : α × σ → ℝ) (G₁ : α × τ → ℝ)
    (hG : ∀ a s' t', R s' t' → G₀ (a, s') = G₁ (a, t')) {s : σ} {t : τ} (hst : R s t) :
    expect (simulate impl₀ c s) G₀ = expect (simulate impl₁ c t) G₁ := by
  induction c generalizing s t with
  | pure a =>
    rw [simulate_pure, simulate_pure, expect_pure, expect_pure]
    exact hG a s t hst
  | query i x k ih =>
    rw [simulate_query, simulate_query, expect_bind, expect_bind]
    exact h i x s t hst _ _ fun y s' t' hR => ih y hR

/-- **Events on the output, from related states:** under the hypothesis of
`expect_simulate_rel`, from related states `R s t` every event `P` on the output of `c` has the
same probability under the two simulations:
`Pr[P (simulate impl₀ c s).1] = Pr[P (simulate impl₁ c t).1]`. For a game that returns a bit
computed from the output this equates the acceptance probabilities (`accept_eq`): a bridging
step [Sho04, §1.1, bridging steps].

**Proof sketch.** Both probabilities are expectations of the indicator of `P` on the output
(`prob_eq_expect`); the two indicators agree at equal outputs whatever the final states, so
`expect_simulate_rel` equates them. -/
theorem prob_simulate_rel (impl₀ : QueryImpl spec σ unifSpec)
    (impl₁ : QueryImpl spec τ unifSpec) (R : σ → τ → Prop)
    (h : ∀ i x s t, R s t → ∀ (g₀ : spec.rng i × σ → ℝ) (g₁ : spec.rng i × τ → ℝ),
      (∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) →
        expect (impl₀ i x s) g₀ = expect (impl₁ i x t) g₁)
    (c : OracleComp spec α) (P : α → Prop) {s : σ} {t : τ} (hst : R s t) :
    prob (simulate impl₀ c s) (fun p => P p.1) = prob (simulate impl₁ c t) (fun p => P p.1) := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_simulate_rel impl₀ impl₁ R h c _ _ (fun _ _ _ _ => rfl) hst

/-- **A sampling call, coupled by a bijection:** let `c₀` draw `u ∈ U` and return `f₀ u`, and
`c₁` draw `v ∈ V` and return `f₁ v`. If a bijection `e : U ≃ V` gives equal answers and related
states, `(f₀ u).1 = (f₁ (e u)).1` and `R (f₀ u).2 (f₁ (e u)).2`, then `c₀` and `c₁` give the same
expectation to any `g₀`, `g₁` that agree at equal answers and related states,
`𝔼[g₀] c₀ = 𝔼[g₁] c₁`: the hypothesis of `expect_simulate_rel` for such a call.

Source: [BGZ09, §4.1, rule R-Rand], adapted: the rule couples two random assignments by a
bijection between equally distributed samplings and establishes the postcondition; here the two
uniform sample types may differ (`e : U ≃ V` between finite types) and the conclusion is stated
as equality of real-valued expectations of tests that agree along `R`, the form
`expect_simulate_rel` consumes.

**Proof sketch.** Both sides are uniform averages (`expect_bind`, `expect_pure`); reindex the
average over `V` along `e` (`expect_sample_equiv`) and compare the two averages pointwise. -/
theorem expect_sample_rel {U V β : Type} [Fintype U] [Nonempty U] [Fintype V] [Nonempty V]
    (R : σ → τ → Prop) (e : U ≃ V) (f₀ : U → β × σ) (f₁ : V → β × τ)
    (hf : ∀ u, (f₀ u).1 = (f₁ (e u)).1 ∧ R (f₀ u).2 (f₁ (e u)).2)
    (g₀ : β × σ → ℝ) (g₁ : β × τ → ℝ) (hg : ∀ y s' t', R s' t' → g₀ (y, s') = g₁ (y, t')) :
    expect ((sample U).bind fun u => .pure (f₀ u)) g₀ =
      expect ((sample V).bind fun v => .pure (f₁ v)) g₁ := by
  rw [expect_bind, expect_bind, ← expect_sample_equiv e]
  refine congrArg _ (funext fun u => ?_)
  dsimp only
  rw [expect_pure, expect_pure]
  calc g₀ (f₀ u) = g₀ ((f₀ u).1, (f₀ u).2) := rfl
    _ = g₁ ((f₀ u).1, (f₁ (e u)).2) := hg _ _ _ (hf u).2
    _ = g₁ (f₁ (e u)) := by rw [(hf u).1]

end ProbComp

end TCSlib.Cryptography.Games
