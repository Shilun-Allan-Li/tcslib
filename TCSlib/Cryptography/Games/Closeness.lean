/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical closeness and output inclusion of computations

Two relations between computations, the per-experiment half of the coin-sampling bridge
(`TCSlib.Cryptography.CoinSampling`).

* **Closeness** `ProbComp.Close ε c₁ c₂`: every test of the output with values in `[0, 1]` has
  expectations differing by at most `ε`. With `[0, 1]`-valued tests in place of events, the
  relation is closed under sequencing (`Close.bind`) and under oracle simulation
  (`Close.simulate`, `m` queries cost `m · ε`), so replacing exact draws by approximate draws
  anywhere in a game moves its acceptance probability by at most the summed per-draw bounds
  (`Close.abs_accept_sub_le`, `advantage_le_of_close`).
* **Output inclusion** `OracleComp.OutputsSubset c₁ c₂`: every property that holds at all
  possible outputs of `c₂` holds at all possible outputs of `c₁`. It is closed under sequencing
  and simulation, so every-outcome properties (perfect correctness and the like) transfer
  exactly along it.

## Main definitions

* `Games.ProbComp.Close ε c₁ c₂`: `|𝔼_{c₁} g − 𝔼_{c₂} g| ≤ ε` for every `g : α → [0, 1]`.
* `Games.OracleComp.OutputsSubset c₁ c₂`: `∀ P, c₂.AllOutputs P → c₁.AllOutputs P`.

## Main results

* `Games.ProbComp.Close.refl`, `.symm`, `.mono`, `.trans`, `.nonneg`, `close_of_expect_eq`.
* `Games.ProbComp.Close.bind_left`, `.bind_right`, `.bind`, `.map`: sequencing.
* `Games.ProbComp.Close.simulate`: `m` queries to `ε`-close implementations are `m · ε`-close.
* `Games.ProbComp.Close.abs_prob_sub_le`, `.abs_accept_sub_le`, `Games.advantage_le_of_close`.
* `Games.OracleComp.allOutputs_bind_iff`: the converse of `AllOutputs.bind`.
* `Games.OracleComp.OutputsSubset.refl`, `.trans`, `.bind`, `.simulate`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 181.1 (`ε`-closeness: every distinguisher's acceptance probabilities differ by at
  most `ε`).
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
  ePrint 2004/332, revision of 18 January 2006, §1.1 (bridging steps and the difference lemma).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Lemma 3.1 (statistical distance bounds every distinguishing advantage).

**Deviation.** [PS10, Definition 181.1] quantifies over distinguishers (events); `Close` uses
`[0, 1]`-valued tests, which bound the same event differences (`Close.abs_prob_sub_le`) and
make the relation closed under `bind`. The interop reader with `EpsClose` of the output laws
(design r1 §4.3, optional) is not in this file.
-/

namespace TCSlib.Cryptography.Games

variable {ι : Type} {α β σ : Type}

namespace ProbComp

/-- **Statistical closeness of computations**: `c₁` and `c₂` are `ε`-close when every function
`g` of the output with values in `[0, 1]` has expectations differing by at most `ε`,
`|𝔼_{c₁} g − 𝔼_{c₂} g| ≤ ε`. [PS10, Definition 181.1] for computations, with `[0, 1]`-valued
tests in place of distinguishers so that the relation is closed under sequencing. -/
def Close (ε : ℝ) (c₁ c₂ : ProbComp α) : Prop :=
  ∀ g : α → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ 1) → |expect c₁ g - expect c₂ g| ≤ ε

/-- `Close ε c₁ c₂ ↔ ∀ g ∈ [0,1]^α, |𝔼_{c₁} g − 𝔼_{c₂} g| ≤ ε`. -/
theorem close_iff (ε : ℝ) (c₁ c₂ : ProbComp α) :
    Close ε c₁ c₂ ↔ ∀ g : α → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ 1) →
      |expect c₁ g - expect c₂ g| ≤ ε := Iff.rfl

/-- A test with values in `[0, 1]` has its expectation in `[0, 1]` (`expect_nonneg`,
`expect_mono`, `expect_const`). Glue. -/
theorem expect_mem_unit (c : ProbComp α) {g : α → ℝ} (hg : ∀ a, 0 ≤ g a ∧ g a ≤ 1) :
    0 ≤ expect c g ∧ expect c g ≤ 1 :=
  ⟨expect_nonneg c fun a => (hg a).1,
    (expect_mono c fun a => (hg a).2).trans (expect_const c 1).le⟩

/-- A closeness bound is nonnegative (the test `g = 0`). -/
theorem Close.nonneg {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) : 0 ≤ ε :=
  (abs_nonneg _).trans (h (fun _ => 0) fun _ => ⟨le_rfl, zero_le_one⟩)

/-- Every computation is `0`-close to itself. -/
theorem Close.refl (c : ProbComp α) : Close 0 c c := fun g _ => by
  rw [sub_self, abs_zero]

/-- Closeness is symmetric. -/
theorem Close.symm {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) : Close ε c₂ c₁ :=
  fun g hg => by
    rw [abs_sub_comm]
    exact h g hg

/-- A closeness bound may be weakened. -/
theorem Close.mono {ε ε' : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) (hε : ε ≤ ε') :
    Close ε' c₁ c₂ := fun g hg => (h g hg).trans hε

/-- Closeness bounds add along a chain (triangle inequality): the statistical bridging steps
of [Sho04, §1.1] compose. -/
theorem Close.trans {ε ε' : ℝ} {c₁ c₂ c₃ : ProbComp α} (h : Close ε c₁ c₂)
    (h' : Close ε' c₂ c₃) : Close (ε + ε') c₁ c₃ := fun g hg =>
  (abs_sub_le _ _ _).trans (add_le_add (h g hg) (h' g hg))

/-- Computations with the same expectations are `0`-close; with `expect_simulate_congr` this
is how exact identities enter a chain of hops. -/
theorem close_of_expect_eq {c₁ c₂ : ProbComp α} (h : ∀ g, expect c₁ g = expect c₂ g) :
    Close 0 c₁ c₂ := fun g _ => by
  rw [h g, sub_self, abs_zero]

/-- **Sequencing on the left**: if `c₁` and `c₂` are `ε`-close, so are `c₁ >>= f` and
`c₂ >>= f`: the test `a ↦ 𝔼_{f a} g` has values in `[0, 1]` (`expect_bind`). -/
theorem Close.bind_left {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) (f : α → ProbComp β) :
    Close ε (c₁.bind f) (c₂.bind f) := fun g hg => by
  rw [expect_bind, expect_bind]
  exact h _ fun a => expect_mem_unit (f a) hg

/-- **Sequencing on the right**: if `f₁ a` and `f₂ a` are `ε`-close for every `a`, so are
`c >>= f₁` and `c >>= f₂` (`expect_bind`, `abs_expect_sub_le`). -/
theorem Close.bind_right {ε : ℝ} (c : ProbComp α) {f₁ f₂ : α → ProbComp β}
    (h : ∀ a, Close ε (f₁ a) (f₂ a)) : Close ε (c.bind f₁) (c.bind f₂) := fun g hg => by
  rw [expect_bind, expect_bind]
  exact abs_expect_sub_le c fun a => h a g hg

/-- **Sequencing**: `ε`-close first steps and `ε'`-close continuations give `(ε + ε')`-close
sequences (`bind_left`, `bind_right`, `trans`). -/
theorem Close.bind {ε ε' : ℝ} {c₁ c₂ : ProbComp α} {f₁ f₂ : α → ProbComp β}
    (h : Close ε c₁ c₂) (h' : ∀ a, Close ε' (f₁ a) (f₂ a)) :
    Close (ε + ε') (c₁.bind f₁) (c₂.bind f₂) :=
  (h.bind_left f₁).trans (Close.bind_right c₂ h')

/-- Post-processing keeps closeness: `Close ε (k <$> c₁) (k <$> c₂)` (`expect_map`). -/
theorem Close.map {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) (k : α → β) :
    Close ε (k <$> c₁) (k <$> c₂) := fun g hg => by
  rw [expect_map, expect_map]
  exact h _ fun a => hg (k a)

/-- Events move by at most `ε`: `|Pr_{c₁}[p] − Pr_{c₂}[p]| ≤ ε` (the indicator of `p` is a
test), the distinguisher form of [PS10, Definition 181.1]. -/
theorem Close.abs_prob_sub_le {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) (p : α → Prop) :
    |prob c₁ p - prob c₂ p| ≤ ε := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact h _ fun a => by
    by_cases hp : p a
    · rw [if_pos hp]
      exact ⟨zero_le_one, le_rfl⟩
    · rw [if_neg hp]
      exact ⟨le_rfl, zero_le_one⟩

/-- **Oracle simulation**: if every call of `impl₀` is `ε`-close to the same call of `impl₁`
(with `0 ≤ ε`), then for a computation with at most `m` queries the two simulations are
`m · ε`-close. The `ε = 0` case is `expect_simulate_congr`.

**Deviation from the design skeleton:** the hypothesis `0 ≤ ε` is added; without it the
statement fails for a computation without queries over an oracle family with no oracles.

**Proof sketch.** Induction on the computation with its budget, as in `prob_bad_le`. A return
gives equal computations. At a query (budget `m ≥ 1`), sequence the `ε`-close calls with the
continuations, which are `(m − 1) · ε`-close by induction (`Close.bind`), and
`ε + (m − 1) · ε = m · ε`. -/
theorem Close.simulate {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec} {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ i x s, Close ε (impl₀ i x s) (impl₁ i x s)) (c : OracleComp spec α)
    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ) :
    Close (m * ε) (Games.simulate impl₀ c s) (Games.simulate impl₁ c s) := by
  induction c generalizing m s with
  | pure a =>
    rw [simulate_pure, simulate_pure]
    exact (Close.refl _).mono (mul_nonneg (Nat.cast_nonneg m) hε)
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    rw [simulate_query, simulate_query]
    have hstep := Close.bind (h i x s) fun ys => ih ys.1 (m - 1) (hk ys.1) ys.2
    refine hstep.mono (le_of_eq ?_)
    have hm' : ((m - 1 : ℕ) : ℝ) = m - 1 := by
      rw [Nat.cast_sub hm, Nat.cast_one]
    rw [hm']
    ring

end ProbComp

/-- Acceptance probabilities of `ε`-close games differ by at most `ε`
(`Close.abs_prob_sub_le` at the event `· = true`). -/
theorem ProbComp.Close.abs_accept_sub_le {ε : ℝ} {G₁ G₂ : ProbComp Bool}
    (h : ProbComp.Close ε G₁ G₂) : |accept G₁ - accept G₂| ≤ ε := by
  rw [accept_eq, accept_eq]
  exact h.abs_prob_sub_le _

/-- **Advantage transfer**: replacing each of two games by an `ε_b`-close one changes the
distinguishing advantage by at most `ε₀ + ε₁`: `advantage G₀' G₁' ≤ advantage G₀ G₁ + ε₀ + ε₁`
[Gar26, Lemma 3.1] (statistical distance bounds every advantage), with the triangle
inequality. -/
theorem advantage_le_of_close {ε₀ ε₁ : ℝ} {G₀ G₁ G₀' G₁' : ProbComp Bool}
    (h₀ : ProbComp.Close ε₀ G₀' G₀) (h₁ : ProbComp.Close ε₁ G₁' G₁) :
    advantage G₀' G₁' ≤ advantage G₀ G₁ + ε₀ + ε₁ := by
  rw [advantage_eq, advantage_eq]
  have e₀ := h₀.abs_accept_sub_le
  have e₁ := h₁.abs_accept_sub_le
  have e₁' : |accept G₁ - accept G₁'| ≤ ε₁ := by
    rw [abs_sub_comm]
    exact e₁
  have t₁ := abs_sub_le (accept G₀') (accept G₀) (accept G₁')
  have t₂ := abs_sub_le (accept G₀) (accept G₁) (accept G₁')
  linarith

namespace OracleComp

variable {spec : OracleSpec ι}

/-- **Output inclusion**: every possible output of `c₁` is a possible output of `c₂`, read
through predicates: whatever holds at all outputs of `c₂` holds at all outputs of `c₁`. The
relation along which perfect correctness and every other `AllOutputs` property transfer.
Glue: no textbook counterpart. -/
def OutputsSubset (c₁ c₂ : OracleComp spec α) : Prop :=
  ∀ P : α → Prop, c₂.AllOutputs P → c₁.AllOutputs P

/-- `OutputsSubset c₁ c₂ ↔ ∀ P, c₂.AllOutputs P → c₁.AllOutputs P`. -/
theorem outputsSubset_iff (c₁ c₂ : OracleComp spec α) :
    OutputsSubset c₁ c₂ ↔ ∀ P : α → Prop, c₂.AllOutputs P → c₁.AllOutputs P := Iff.rfl

/-- **Possible outputs of a sequence**, in both directions: `(c >>= f).AllOutputs Q` iff every
possible output `a` of `c` has `(f a).AllOutputs Q`. The `←` direction is `AllOutputs.bind`;
`→` is an induction on `c` (a return is `f a`; a query passes to every continuation). -/
theorem allOutputs_bind_iff {c : OracleComp spec α} {f : α → OracleComp spec β}
    {Q : β → Prop} : (c.bind f).AllOutputs Q ↔ c.AllOutputs fun a => (f a).AllOutputs Q := by
  refine ⟨fun h => ?_, fun h => AllOutputs.bind h fun _ ha => ha⟩
  induction c with
  | pure a =>
    rw [pure_bind] at h
    exact allOutputs_pure.2 h
  | query i x k ih =>
    rw [query_bind] at h
    exact allOutputs_query.2 fun y => ih y (allOutputs_query.1 h y)

/-- Output inclusion is reflexive. -/
theorem OutputsSubset.refl (c : OracleComp spec α) : OutputsSubset c c := fun _ h => h

/-- Output inclusion is transitive. -/
theorem OutputsSubset.trans {c₁ c₂ c₃ : OracleComp spec α} (h : OutputsSubset c₁ c₂)
    (h' : OutputsSubset c₂ c₃) : OutputsSubset c₁ c₃ := fun P hP => h P (h' P hP)

/-- **Sequencing**: included first steps and included continuations give included sequences:
`allOutputs_bind_iff` on `c₂ >>= f₂`, then `h` with the predicate `a ↦ (f₂ a).AllOutputs P`,
then `h'` pointwise and `AllOutputs.bind`. -/
theorem OutputsSubset.bind {c₁ c₂ : OracleComp spec α} {f₁ f₂ : α → OracleComp spec β}
    (h : OutputsSubset c₁ c₂) (h' : ∀ a, OutputsSubset (f₁ a) (f₂ a)) :
    OutputsSubset (c₁.bind f₁) (c₂.bind f₂) := fun P hP =>
  AllOutputs.bind (h _ (allOutputs_bind_iff.1 hP)) fun a ha => h' a P ha

/-- **Oracle simulation**: implementations whose every call is output-included give
output-included simulations (induction on the computation, `OutputsSubset.bind`). -/
theorem OutputsSubset.simulate {ι' : Type} {spec' : OracleSpec ι'} {spec'' : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec' σ spec''}
    (h : ∀ i x s, OutputsSubset (impl₀ i x s) (impl₁ i x s)) (c : OracleComp spec' α) (s : σ) :
    OutputsSubset (Games.simulate impl₀ c s) (Games.simulate impl₁ c s) := by
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, simulate_pure]
    exact OutputsSubset.refl _
  | query i x k ih =>
    rw [simulate_query, simulate_query]
    exact OutputsSubset.bind (h i x s) fun ys => ih ys.1 ys.2

end OracleComp

end TCSlib.Cryptography.Games
