/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic computations

Randomness enters the framework as one more oracle: oracle `m` of `unifSpec` answers a uniformly
random element of `Fin (m + 1)`, and a uniform element of any nonempty finite type is obtained
through an enumeration. A *probabilistic computation* (`ProbComp`) is an oracle computation whose
only oracle is this one. Security games, once their adversary is plugged in and their oracles
implemented, are probabilistic computations.

The semantics is elementary and real-valued. The expectation of `g` over the output of a
computation is defined by recursion on the computation: a return contributes `g a`, and a sampling
step averages over its `m + 1` equally likely answers. There are no measures and no extended
reals: every computation is a finite tree with finite branching, so every probability is a finite
sum of rationals. The probability of an event is the expectation of its indicator. For a
computation with a finite output type, its output distribution is a `FinDist` of the library's
information-theory layer, so statistical distance and closeness (`EpsClose`) apply directly.

## Main definitions

* `Games.unifSpec`: the uniform-sampling oracles; `Games.ProbComp`: computations over them.
* `Games.ProbComp.sampleFin m`, `Games.ProbComp.sample T`: a uniform element of `Fin (m + 1)`, and
  of a nonempty finite type `T`.
* `Games.ProbComp.expect c g`: the expectation of `g` over the output of `c`.
* `Games.ProbComp.prob c p`: the probability that the output of `c` satisfies `p`.
* `Games.ProbComp.dist c`: the output distribution of `c`, for a finite output type.

## Main results

* `ProbComp.expect_bind`: **total expectation**; sequencing averages the continuations.
* `ProbComp.expect_sample`: sampling a finite type is the uniform average.
* `ProbComp.expect_add`, `expect_const_mul`, `expect_sum`, `expect_mono`: linearity and
  monotonicity.
* `ProbComp.prob_nonneg`, `prob_le_one`, `prob_mono`, `prob_or_le` (the union bound),
  `prob_not`, `prob_bind`.
* `ProbComp.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`,
  `expect_sample_update`, `expect_sample_coord`: reindexing, exchanging and resampling uniform
  samples; `expect_sub`, `abs_expect_sub_le`: subtraction and pointwise closeness.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
  Uniform sampling as an oracle follows VCVio's uniform-selection oracle; the real-valued
  finite-sum semantics here is not VCVio's (which is measure-valued).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (probabilistic algorithms; the uniform distribution over coin strings).
-/

namespace TCSlib.Cryptography.Games

open Finset TCSlib.InformationTheory

/-! Seal A (dl-folds, base): a verbatim copy of `TCSlib/Cryptography/Games/Probability.lean`, with every seal candidate of its
full TCSlib import closure (15 definitions, `PolyExpr.eval` exempt) irreducible from here on. -/
attribute [local irreducible] _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform


/-- The **uniform-sampling oracles**: oracle `m` takes no query and answers a uniformly random
element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp] -/
abbrev unifSpec : OracleSpec ℕ := ⟨fun _ => Unit, fun m => Fin (m + 1)⟩

/-- **Probabilistic computations**: oracle computations whose only oracles draw uniform samples.
[VCVio, OracleComp/ProbComp/Basic] -/
abbrev ProbComp := OracleComp unifSpec

namespace ProbComp

variable {α β : Type}

/-- A uniformly random element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp/Basic (uniformFin)] -/
def sampleFin (m : ℕ) : ProbComp (Fin (m + 1)) := .query m () .pure

/-- Sampling `Fin (m + 1)` is one query to the `m`-th sampling oracle:
`sampleFin m = .query m () .pure`. -/
theorem sampleFin_eq (m : ℕ) : sampleFin m = .query m () .pure := rfl

/-- A uniformly random element of the nonempty finite type `T`, through its enumeration
`Fintype.equivFin`. -/
noncomputable def sample (T : Type) [Fintype T] [Nonempty T] : ProbComp T :=
  (fun j : Fin (Fintype.card T - 1 + 1) =>
    (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
      sampleFin (Fintype.card T - 1)

/-- Sampling `T` is sampling an index below `|T|` and reading it through `Fintype.equivFin`:
`sample T = (fun j => (equivFin T).symm (Fin.cast _ j)) <$> sampleFin (|T| − 1)`. -/
theorem sample_eq (T : Type) [Fintype T] [Nonempty T] :
    sample T = (fun j : Fin (Fintype.card T - 1 + 1) =>
      (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
        sampleFin (Fintype.card T - 1) := rfl

/-- The **expectation** of `g` over the output of `c`: `g a` for a return, and the average over
the `m + 1` equally likely answers at a sampling step. -/
noncomputable def expect : ProbComp α → (α → ℝ) → ℝ
  | .pure a, g => g a
  | .query m _ k, g => ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g

/-- The **probability** that the output of `c` satisfies `p`: the expectation of the indicator
of `p`. -/
noncomputable def prob (c : ProbComp α) (p : α → Prop) : ℝ := by
  classical exact expect c (fun a => if p a then 1 else 0)

/-- A return is its own expectation. -/
@[simp] theorem expect_pure (a : α) (g : α → ℝ) : expect (.pure a) g = g a := rfl

/-- A sampling step averages over its answers. -/
theorem expect_query (m : ℕ) (x : Unit) (k : Fin (m + 1) → ProbComp α) (g : α → ℝ) :
    expect (.query m x k) g = ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g := rfl

/-- **Total expectation:** the expectation over `c` followed by `f` is the expectation over `c`
of the expectation over `f a`.

**Proof sketch.** Induction on `c`: a return is immediate, and at a sampling step both sides
average the same continuations. -/
theorem expect_bind (c : ProbComp α) (f : α → ProbComp β) (g : β → ℝ) :
    expect (c.bind f) g = expect c (fun a => expect (f a) g) := by
  induction c with
  | pure a => simp only [OracleComp.pure_bind, expect_pure]
  | query m x k ih => simp only [OracleComp.query_bind, expect_query, ih]

/-- The expectation over a mapped computation is the expectation of the composite. -/
theorem expect_map (h : α → β) (c : ProbComp α) (g : β → ℝ) :
    expect (h <$> c) g = expect c (fun a => g (h a)) := by
  rw [OracleComp.map_eq_bind, expect_bind]; rfl

/-- Sampling `Fin (m + 1)` is the uniform average over it. -/
theorem expect_sampleFin (m : ℕ) (g : Fin (m + 1) → ℝ) :
    expect (sampleFin m) g = ((m : ℝ) + 1)⁻¹ * ∑ j, g j := rfl

/-- Sampling a nonempty finite type is the uniform average over it.

**Proof sketch.** The sample is the image of a uniform element of `Fin |T|` under the bijection
`Fintype.equivFin`, and a sum is invariant under reindexing by a bijection. -/
theorem expect_sample (T : Type) [Fintype T] [Nonempty T] (g : T → ℝ) :
    expect (sample T) g = (Fintype.card T : ℝ)⁻¹ * ∑ t, g t := by
  have hc : Fintype.card T - 1 + 1 = Fintype.card T := Nat.sub_add_cancel Fintype.card_pos
  rw [sample, expect_map, expect_sampleFin]
  congr 1
  · congr 1
    exact_mod_cast hc
  · exact Fintype.sum_equiv ((finCongr hc).trans (Fintype.equivFin T).symm) _ _
      (fun j => by simp)

/-- Expectation is additive. -/
theorem expect_add (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a + g a) = expect c f + expect c g := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [expect_query, ih, sum_add_distrib, mul_add]

/-- Expectation commutes with scaling by a constant. -/
theorem expect_const_mul (c : ProbComp α) (r : ℝ) (f : α → ℝ) :
    expect c (fun a => r * f a) = r * expect c f := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, ← mul_sum]
    ring

/-- The expectation of a constant is that constant. -/
theorem expect_const (c : ProbComp α) (r : ℝ) : expect c (fun _ => r) = r := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

/-- Expectation commutes with finite sums. -/
theorem expect_sum {ι : Type} (c : ProbComp α) (s : Finset ι) (f : ι → α → ℝ) :
    expect c (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect c (f i) := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, mul_sum]
    exact sum_comm

/-- Expectation is monotone. -/
theorem expect_mono (c : ProbComp α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expect c f ≤ expect c g := by
  induction c with
  | pure a => exact h a
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j) (by positivity)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (c : ProbComp α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ expect c f := by
  simpa [expect_const] using expect_mono c (f := fun _ => 0) h

/-! ### Probabilities of events -/

/-- The probability of `p` is the expectation of its indicator (any decidability instance). -/
theorem prob_eq_expect (c : ProbComp α) (p : α → Prop) [DecidablePred p] :
    prob c p = expect c (fun a => if p a then 1 else 0) := by
  unfold prob
  congr 1
  funext a
  congr 1

/-- A return satisfies `p` with probability one or zero. -/
theorem prob_pure (a : α) (p : α → Prop) [Decidable (p a)] :
    prob (.pure a) p = if p a then 1 else 0 := by
  classical
  rw [prob_eq_expect, expect_pure]
  congr 1

/-- **Total probability:** the probability over `c` followed by `f` is the expectation over `c`
of the probability over `f a`. -/
theorem prob_bind (c : ProbComp α) (f : α → ProbComp β) (p : β → Prop) :
    prob (c.bind f) p = expect c (fun a => prob (f a) p) := by
  classical
  simp only [prob_eq_expect, expect_bind]

/-- Probabilities are nonnegative. -/
theorem prob_nonneg (c : ProbComp α) (p : α → Prop) : 0 ≤ prob c p := by
  classical
  rw [prob_eq_expect]
  exact expect_nonneg c fun a => by split_ifs <;> norm_num

/-- Probabilities are at most one. -/
theorem prob_le_one (c : ProbComp α) (p : α → Prop) : prob c p ≤ 1 := by
  classical
  rw [prob_eq_expect]
  calc expect c (fun a => if p a then (1 : ℝ) else 0) ≤ expect c (fun _ => 1) :=
        expect_mono c fun a => by split_ifs <;> norm_num
    _ = 1 := expect_const c 1

/-- An event implied by another has at least its probability. -/
theorem prob_mono (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    prob c p ≤ prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_mono c fun a => by
    by_cases hp : p a
    · simp [hp, h a hp]
    · simp only [hp, if_false]; split_ifs <;> norm_num

/-- Events that agree on every output have the same probability. -/
theorem prob_congr (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    prob c p = prob c q :=
  le_antisymm (prob_mono c fun a => (h a).1) (prob_mono c fun a => (h a).2)

/-- **The union bound** for two events. -/
theorem prob_or_le (c : ProbComp α) (p q : α → Prop) :
    prob c (fun a => p a ∨ q a) ≤ prob c p + prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  exact expect_mono c fun a => by
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- The complement of an event has one minus its probability. -/
theorem prob_not (c : ProbComp α) (p : α → Prop) :
    prob c (fun a => ¬ p a) = 1 - prob c p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, eq_sub_iff_add_eq, ← expect_add]
  calc expect c (fun a => (if ¬ p a then (1 : ℝ) else 0) + if p a then 1 else 0)
      = expect c (fun _ => 1) := by
        congr 1; funext a; by_cases hp : p a <;> simp [hp]
    _ = 1 := expect_const c 1

/-! ### Output distributions -/

/-- The **output distribution** of a computation with a finite output type: the probability of
each outcome. -/
noncomputable def dist [Fintype α] [DecidableEq α] (c : ProbComp α) : FinDist α where
  prob a := prob c (· = a)
  nonneg a := prob_nonneg c _
  sum_prob := by
    simp only [prob_eq_expect]
    rw [← expect_sum]
    calc expect c (fun x => ∑ a, if x = a then (1 : ℝ) else 0) = expect c (fun _ => 1) := by
          congr 1; funext x; simp
      _ = 1 := expect_const c 1

/-- The output distribution gives each outcome its probability. -/
theorem dist_apply [Fintype α] [DecidableEq α] (c : ProbComp α) (a : α) :
    dist c a = prob c (· = a) := rfl

/-! ### Sampling identities -/

section Sampling

variable {β : Type}

/-- **Reindexing a sample by an equivalence:** `𝔼_{a ← α} g (e a) = 𝔼_{b ← β} g b`.

**Proof sketch.** Both are uniform averages (`expect_sample`); the cardinalities agree
(`Fintype.card_congr`) and the sums agree by reindexing along `e` (`Equiv.sum_comp`). -/
theorem expect_sample_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β)
    (g : β → ℝ) : expect (sample α) (fun a => g (e a)) = expect (sample β) g := by
  rw [expect_sample, expect_sample, Fintype.card_congr e, Equiv.sum_comp e g]

/-- **Independent samples commute:**
`𝔼_{a ← α} 𝔼_{b ← β} g a b = 𝔼_{b ← β} 𝔼_{a ← α} g a b`.

**Proof sketch.** Both sides are the double uniform average (`expect_sample`); exchange the two
finite sums (`Finset.sum_comm`). -/
theorem expect_sample_comm [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α → β → ℝ) :
    (expect (sample α) fun a => expect (sample β) fun b => g a b) =
      expect (sample β) fun b => expect (sample α) fun a => g a b := by
  simp only [expect_sample, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  ring

/-- **Sampling a singleton type** returns its element: `𝔼_{a ← α} g a = g default`. -/
theorem expect_sample_unique [Fintype α] [Unique α] (g : α → ℝ) :
    expect (sample α) g = g default := by
  rw [expect_sample, Fintype.card_unique, Fintype.sum_unique]
  simp

/-- Expectation is subtractive: `𝔼[f − g] = 𝔼 f − 𝔼 g`. -/
theorem expect_sub (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a - g a) = expect c f - expect c g := by
  have h := expect_add c f (fun a => -1 * g a)
  rw [expect_const_mul] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-- **Resampling one coordinate of a uniform tuple leaves it uniform**:
`𝔼_{v} 𝔼_{b} f (update v j b) = 𝔼_{v} f v`.

**Proof sketch.** The map `(v, b) ↦ (update v j b, v j)` is an involution of `(ι → β) × β`
(`Function.update_idem`, `Function.update_eq_self`). Written as uniform averages
(`expect_sample`), the double sum of `f (update v j b)` over pairs is the sum of `f v` over pairs
reindexed along it (`Fintype.sum_prod_type'`, `Equiv.sum_comp`), which is `|β|` times the sum of
`f`. -/
theorem expect_sample_update {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (j : ι) (f : (ι → β) → ℝ) :
    (expect (sample (ι → β)) fun v => expect (sample β) fun b => f (Function.update v j b)) =
      expect (sample (ι → β)) f := by
  let e : (ι → β) × β ≃ (ι → β) × β :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      right_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
  have hpair : (∑ v : ι → β, ∑ b : β, f (Function.update v j b)) =
      ∑ v : ι → β, ∑ _b : β, f v := by
    rw [← Fintype.sum_prod_type' (fun v b => f (Function.update v j b)),
      ← Fintype.sum_prod_type' (fun v (_ : β) => f v)]
    exact Equiv.sum_comp e (fun p => f p.1)
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by positivity
  simp only [expect_sample, ← mul_sum]
  rw [hpair]
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  rw [inv_mul_cancel_left₀ hβ]

/-- **One coordinate of a uniform tuple, sampled apart:** if `F r T` does not depend on the
coordinate `j` of `T`, then `𝔼_{T} F (T j) T = 𝔼_{r} 𝔼_{T} F r T`.

**Proof sketch.** Exchange the samples on the right (`expect_sample_comm`) and resample the
coordinate `j` on the left (`expect_sample_update`); pointwise,
`F ((update T j r) j) (update T j r) = F r T` (`Function.update_self` and the hypothesis). -/
theorem expect_sample_coord {ι : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (j : ι) (F : β → (ι → β) → ℝ) (hF : ∀ r r' T, F r (Function.update T j r') = F r T) :
    expect (sample (ι → β)) (fun T => F (T j) T) =
      expect (sample β) fun r => expect (sample (ι → β)) fun T => F r T := by
  rw [expect_sample_comm, ← expect_sample_update j (fun T => F (T j) T)]
  refine congrArg _ (funext fun T => congrArg _ (funext fun r => ?_))
  rw [Function.update_self, hF]

/-- Expectations of functions `ε`-close at every point are `ε`-close:
`(∀ x, |f x - g x| ≤ ε) → |𝔼_c f - 𝔼_c g| ≤ ε`. -/
theorem abs_expect_sub_le (c : ProbComp α) {f g : α → ℝ} {ε : ℝ}
    (h : ∀ x, |f x - g x| ≤ ε) : |expect c f - expect c g| ≤ ε := by
  have h1 : expect c f ≤ expect c g + ε :=
    calc expect c f ≤ expect c (fun x => g x + ε) :=
          expect_mono c fun x => by linarith [(abs_le.1 (h x)).2]
      _ = expect c g + ε := by rw [expect_add c g (fun _ => ε), expect_const]
  have h2 : expect c g ≤ expect c f + ε :=
    calc expect c g ≤ expect c (fun x => f x + ε) :=
          expect_mono c fun x => by linarith [(abs_le.1 (h x)).1]
      _ = expect c f + ε := by rw [expect_add c f (fun _ => ε), expect_const]
  rw [abs_le]
  constructor <;> linarith

end Sampling

end ProbComp

end TCSlib.Cryptography.Games
