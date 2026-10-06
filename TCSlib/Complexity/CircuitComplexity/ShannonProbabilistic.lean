/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Distributions.Uniform
import TCSlib.Complexity.CircuitComplexity.DAGHardFunctions

/-!
# Shannon's bound, probabilistic form

[AB09, p. 115] rephrases the counting proof of [AB09, Thm 6.21]: for a uniformly random
`f : {0,1}ⁿ → {0,1}`, the probability that some circuit of size `2ⁿ/(10n)` computes `f` is
at most `2^{0.9·2ⁿ} / 2^{2ⁿ} = 2^{−0.1·2ⁿ}`.  We prove this over the book's model
(`BoolCircuit.DAGCircuit` with fan-in two, size counting every vertex), both as a
counting fraction and as a probability under `PMF.uniformOfFintype`, for **every** `n`, and
we formalize the book's three steps leading to it: (i) a fixed circuit agrees with a random
`f` at a fixed input with probability `1/2`; (ii) by independence over the `2ⁿ` inputs it
computes `f` with probability `2^{-2ⁿ}`; (iii) the union bound over the circuits gives the
count times `2^{-2ⁿ}`, which is how `prob_computableDAG_shannon_le` is proved.

The set `BoolCircuit.computableDAG n S` of functions computed by fan-in-two circuits of
size at most `S` is defined in `DAGHardFunctions.lean`.

## Main results

* `BoolCircuit.prob_eval_eq_apply` — step (i): `Pr_f[C(x) = f(x)] = 1/2`.
* `BoolCircuit.prob_computes`, `BoolCircuit.prob_computes_eq_prod` — step (ii):
  `Pr_f[C computes f] = 2^{-2ⁿ}`, the product of the step-(i) probabilities.
* `BoolCircuit.prob_exists_eq_le` — the union bound over any finite description set.
* `BoolCircuit.prob_computableDAG_le`, `BoolCircuit.prob_computableDAG_le_count` —
  step (iii): `Pr_f[some size-≤ S circuit computes f] ≤ #(circuits) · 2^{-2ⁿ}`.
* `BoolCircuit.computableDAG_shannon_fraction_le` —
  `|computableDAG n ⌊2ⁿ/(10n)⌋| / 2^{2ⁿ} ≤ 2^{−2ⁿ/10}` for every `n`.
* `BoolCircuit.prob_computableDAG_shannon_le` — the same as a probability for a uniformly
  random function.
* `BoolCircuit.computableDAG_real_cutoff` — reading the cutoff `2ⁿ/(10n)` as a real
  number gives the same set, so the `⌊·⌋` costs nothing.

## Divergences from [AB09, p. 115]

* **Range of `n`.**  The book's statement is asymptotic ("tends very fast to zero"); the
  bound holds for all `n`.  For `n ≤ 9` it is trivial — the cutoff is below `n`, the least
  size of a circuit, so no function is counted (for `n ≤ 5` the cutoff is `0`); the proof
  uses the description count of `DAGHardFunctions.lean` whenever the cutoff is positive
  (`n ≥ 6`).
* **Counting.**  [AB09] counts `2^{9 S log S}` adjacency-list encodings; we use
  `card_computable_dag_le`'s `(S + 1)(3(S + 1)²)^S S ≤ 2^{2n(S + 1)}`, which is at most
  `2^{0.9·2ⁿ}` exactly when the book's estimate is needed.
* **Union index.**  Step (iii) unions over the *functions* computed by small circuits (the
  event "`C` computes `f`" depends only on `C`'s function); their number is bounded by the
  description count, so the bound is at most the book's union over circuits.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.5, Theorem 6.21 and p. 115.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-- The number of functions computed by circuits of size at most `S = 2ⁿ/(10n)` is at most
`2 ^ (2n(S + 1))`, and `20 n (S + 1) ≤ 9 · 2ⁿ`, whenever `S ≥ 1`.

**Proof sketch.** The counting bound for size-`S` circuits gives at most
`(S+1)(3(S+1)²)^S · S` computable functions, which is at most `(2(S+1))^{2(S+1)}` since
`(S+1)S ≤ (2(S+1))²` and `3(S+1)² ≤ (2(S+1))²`. From `10 n S ≤ 2ⁿ` and `S ≥ 1` we get
`2(S+1) ≤ 2ⁿ`, so the count is at most `(2ⁿ)^{2(S+1)} = 2^{2n(S+1)}`. The second
conjunct `20 n (S+1) ≤ 9 · 2ⁿ` is nonlinear arithmetic from the same hypotheses
(using `10 n ≤ 2ⁿ`). -/
private theorem count_le_pow {n S : ℕ} (hn1 : 1 ≤ n) (hS0 : 1 ≤ S) (hS : 10 * n * S ≤ 2 ^ n) :
    (computableDAG n S).ncard ≤ 2 ^ (n * (2 * (S + 1))) ∧ 20 * n * (S + 1) ≤ 9 * 2 ^ n := by
  have h1 : (S + 1) * (3 * (S + 1) ^ 2) ^ S * S ≤ (2 * (S + 1)) ^ (2 * (S + 1)) := by
    calc (S + 1) * (3 * (S + 1) ^ 2) ^ S * S = ((S + 1) * S) * (3 * (S + 1) ^ 2) ^ S := by
          ring
      _ ≤ (2 * (S + 1)) ^ 2 * ((2 * (S + 1)) ^ 2) ^ S := by
          apply Nat.mul_le_mul
          · nlinarith
          · exact Nat.pow_le_pow_left (by nlinarith) _
      _ = (2 * (S + 1)) ^ (2 * (S + 1)) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          ring
  have hn : 10 * n ≤ 2 ^ n := by nlinarith
  have : 10 * S ≤ 10 * n * S := by nlinarith
  have h2 : 2 * (S + 1) ≤ 2 ^ n := by omega
  refine ⟨?_, by nlinarith⟩
  calc (computableDAG n S).ncard ≤ (S + 1) * (3 * (S + 1) ^ 2) ^ S * S :=
        card_computable_dag_le n S
    _ ≤ (2 * (S + 1)) ^ (2 * (S + 1)) := h1
    _ ≤ (2 ^ n) ^ (2 * (S + 1)) := Nat.pow_le_pow_left h2 _
    _ = 2 ^ (n * (2 * (S + 1))) := by rw [← pow_mul]

/-- **Shannon's bound, probabilistic form.**  For every `n`, at most a
`2 ^ (-2ⁿ/10)` fraction of the `2 ^ 2ⁿ` Boolean functions on `n` bits is computed by a
fan-in-two circuit of size at most `2ⁿ/(10n)`: for a uniformly random `f`,
`Pr[∃ C, |C| ≤ 2ⁿ/(10n), C computes f] ≤ 2 ^ (-0.1 · 2ⁿ)`.  [AB09, p. 115], the
rephrasing of [AB09, Thm 6.21]

The book states this asymptotically ("a number that tends very fast to zero"); it holds
for **every** `n`, with no lower bound on `n`.  For `n ≤ 5` the cutoff `⌊2ⁿ/(10n)⌋` is `0`
and for `6 ≤ n ≤ 9` it is below `n`, the least size of a circuit, so no function is
counted; from `n = 10` on the counting bound does the work.

**Proof sketch.** Put `S = ⌊2ⁿ/(10n)⌋`.  If `S = 0` nothing is counted.  Otherwise the
descriptions of size-`≤ S` circuits number at most `(2(S + 1)) ^ (2(S + 1)) ≤ 2 ^ (2n(S + 1))`
(`card_computable_dag_le`), and `20n(S + 1) ≤ 2 · 2ⁿ + 20n ≤ 9 · 2ⁿ` because
`10nS ≤ 2ⁿ` and `S ≥ 1` force `10n ≤ 2ⁿ`.  So the fraction is at most
`2 ^ (2n(S + 1) - 2ⁿ) ≤ 2 ^ (-2ⁿ/10)`. -/
theorem computableDAG_shannon_fraction_le (n : ℕ) :
    ((computableDAG n (2 ^ n / (10 * n))).ncard : ℝ) / 2 ^ 2 ^ n ≤
      (2 : ℝ) ^ (-(2 ^ n : ℝ) / 10) := by
  set S := 2 ^ n / (10 * n) with hSdef
  have hS : 10 * n * S ≤ 2 ^ n := Nat.mul_div_le _ _
  have hpos : (0 : ℝ) < 2 ^ 2 ^ n := by positivity
  rcases Nat.eq_zero_or_pos S with hS0 | hS0
  · have h0 : (computableDAG n S).ncard = 0 := by
      have := card_computable_dag_le n S
      rw [hS0] at this
      simpa [computableDAG, hS0] using this
    rw [h0]
    simp only [Nat.cast_zero, zero_div]
    positivity
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [hSdef] at hS0
    · exact h
  obtain ⟨hc, hk⟩ := count_le_pow hn1 hS0 hS
  have hc' : ((computableDAG n S).ncard : ℝ) ≤ (2 : ℝ) ^ (n * (2 * (S + 1))) := by
    exact_mod_cast hc
  rw [div_le_iff₀ hpos]
  calc ((computableDAG n S).ncard : ℝ) ≤ (2 : ℝ) ^ (n * (2 * (S + 1))) := hc'
    _ = (2 : ℝ) ^ ((n * (2 * (S + 1)) : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ (-(2 ^ n : ℝ) / 10 + ((2 ^ n : ℕ) : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : ((20 * n * (S + 1) : ℕ) : ℝ) ≤ ((9 * 2 ^ n : ℕ) : ℝ) := by exact_mod_cast hk
        push_cast at this ⊢
        linarith
    _ = (2 : ℝ) ^ (-(2 ^ n : ℝ) / 10) * 2 ^ 2 ^ n := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast]

/-! ## The probabilistic argument, step by step

[AB09, p. 115]: "for every fixed circuit `C` and input `x`, the probability that
`C(x) = f(x)` is `1/2`, and since these choices are independent, the probability that `C`
computes `f` (i.e., `C(x) = f(x)` for every `x ∈ {0,1}ⁿ`) is `2^{-2ⁿ}`"; then "we can apply
the union bound" over the circuits of size at most `2ⁿ/(10n)`.  Throughout, `f` is drawn
from `PMF.uniformOfFintype ((Fin n → Bool) → Bool)`. -/

section Steps

variable {n : ℕ}

/-- There are `2 ^ 2ⁿ` Boolean functions on `n` bits. -/
theorem card_boolFun : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by simp

/-- For a fixed function `g` and input `x`, a uniformly random `f` agrees with `g` at `x` with
probability `1/2`.

**Proof sketch.** Flipping the value at `x` is a bijection of the functions exchanging those
that agree with `g` at `x` and those that do not, so each set has half of the `2 ^ 2ⁿ`
functions. -/
theorem prob_apply_eq (g : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure {f | f x = g x} = 2⁻¹ := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  set A := {f : (Fin n → Bool) → Bool | f x = g x}
  -- flipping the value at `x` exchanges `A` and its complement
  let σ : ((Fin n → Bool) → Bool) ≃ ((Fin n → Bool) → Bool) :=
    { toFun := fun f => Function.update f x (!f x)
      invFun := fun f => Function.update f x (!f x)
      left_inv := fun f => by funext y; by_cases h : y = x <;> simp [Function.update, h]
      right_inv := fun f => by funext y; by_cases h : y = x <;> simp [Function.update, h] }
  have hσ : Fintype.card {f : (Fin n → Bool) → Bool // f x = g x} =
      Fintype.card {f : (Fin n → Bool) → Bool // ¬ f x = g x} :=
    Fintype.card_congr (σ.subtypeEquiv fun f => by
      show f x = g x ↔ ¬ (Function.update f x (!f x)) x = g x
      simp)
  have hc := Fintype.card_subtype_compl (fun f : (Fin n → Bool) → Bool => f x = g x)
  have hA : Fintype.card A = Fintype.card {f : (Fin n → Bool) → Bool // f x = g x} := rfl
  rw [hA]
  set c := Fintype.card {f : (Fin n → Bool) → Bool // f x = g x}
  have hN : Fintype.card ((Fin n → Bool) → Bool) = 2 * c := by
    have := Fintype.card_subtype_le (fun f : (Fin n → Bool) → Bool => f x = g x)
    omega
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0] at hN; simp at hN
  rw [hN, Nat.cast_mul, Nat.cast_ofNat]
  rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hc0) (by simp), mul_one]

/-- **Step (i).**  For a fixed circuit `C` and input `x`, `Pr_f[C(x) = f(x)] = 1/2`.
[AB09, p. 115] -/
theorem prob_eval_eq_apply (C : DAGCircuit n) (x : Fin n → Bool) :
    (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure {f | f x = C.eval x} =
      2⁻¹ :=
  prob_apply_eq C.eval x

/-- A uniformly random `f` equals a fixed function `g` everywhere with probability
`2 ^ (-2ⁿ)`: the event is the single point `g`. -/
theorem prob_forall_eq (g : (Fin n → Bool) → Bool) :
    (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure {f | ∀ x, f x = g x} =
      2⁻¹ ^ 2 ^ n := by
  have : {f : (Fin n → Bool) → Bool | ∀ x, f x = g x} = {g} := by
    ext f; simp [funext_iff]
  rw [this, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, card_boolFun]
  push_cast
  rw [ENNReal.inv_pow]

/-- **Step (ii).**  A fixed circuit `C` computes a uniformly random `f` with probability
`2 ^ (-2ⁿ)`.  [AB09, p. 115] -/
theorem prob_computes (C : DAGCircuit n) :
    (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure {f | ∀ x, f x = C.eval x} =
      2⁻¹ ^ 2 ^ n :=
  prob_forall_eq C.eval

/-- **The product rule of step (ii).**  The probability that `C` computes `f` (the
intersection of the `2ⁿ` events `C(x) = f(x)`) is the product over the inputs `x` of the
probabilities that `C(x) = f(x)`.  [AB09, p. 115] (the book's "since these choices are
independent"; full mutual independence of the events is not stated) -/
theorem prob_computes_eq_prod (C : DAGCircuit n) :
    (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure {f | ∀ x, f x = C.eval x} =
      ∏ x, (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure
        {f | f x = C.eval x} := by
  simp only [prob_eval_eq_apply, Finset.prod_const, Finset.card_univ, prob_computes]
  simp

/-- **The union bound.**  For any finite set `D` of descriptions, each denoting a function
`e d`, a uniformly random `f` is denoted by some description in `D` with probability at most
`|D| · 2 ^ (-2ⁿ)`.  [AB09, p. 115] -/
theorem prob_exists_eq_le {ι : Type} (D : Finset ι) (e : ι → (Fin n → Bool) → Bool) :
    (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure
        {f | ∃ d ∈ D, ∀ x, f x = e d x} ≤ D.card * 2⁻¹ ^ 2 ^ n := by
  have : {f : (Fin n → Bool) → Bool | ∃ d ∈ D, ∀ x, f x = e d x} =
      ⋃ d ∈ D, {f | ∀ x, f x = e d x} := by
    ext f; simp
  rw [this]
  calc _ ≤ ∑ d ∈ D, (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure
          {f | ∀ x, f x = e d x} := MeasureTheory.measure_biUnion_finset_le D _
    _ = _ := by
      rw [Finset.sum_congr rfl fun d _ => prob_forall_eq (e d), Finset.sum_const, nsmul_eq_mul]

/-- **Step (iii), union bound over the circuits.**  The probability that some fan-in-two
circuit of size at most `S` computes a uniformly random `f` is at most the number of
functions such circuits compute times `2 ^ (-2ⁿ)`.  [AB09, p. 115]

The union runs over the circuits' functions (each circuit's event depends only on its
function); `prob_computableDAG_le_count` bounds their number by the description count. -/
theorem prob_computableDAG_le (n S : ℕ) :
    (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure (computableDAG n S) ≤
      (computableDAG n S).ncard * 2⁻¹ ^ 2 ^ n := by
  set D := (Set.toFinite (computableDAG n S)).toFinset
  have hsub : computableDAG n S ⊆ {f | ∃ g ∈ D, ∀ x, f x = id g x} := fun f hf =>
    ⟨f, by simpa [D] using hf, fun _ => rfl⟩
  calc _ ≤ (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure
          {f | ∃ g ∈ D, ∀ x, f x = id g x} := MeasureTheory.measure_mono hsub
    _ ≤ D.card * 2⁻¹ ^ 2 ^ n := prob_exists_eq_le D id
    _ = _ := by rw [Set.ncard_eq_toFinset_card]

/-- **Step (iii) with the circuit count.**  The probability that some fan-in-two circuit of
size at most `S` computes a uniformly random `f` is at most the number
`(S + 1)(3(S + 1)²)^S · S` of circuit descriptions times `2 ^ (-2ⁿ)`: the union bound of
`prob_computes` over the descriptions.  [AB09, p. 115] (with the description count of
`card_computable_dag_le` for the book's `2^{9 S log S}`)

The union is taken over the computed functions, which are at most as many as the
descriptions, so this bound is at most the union bound over the descriptions themselves. -/
theorem prob_computableDAG_le_count (n S : ℕ) :
    (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure (computableDAG n S) ≤
      ((S + 1) * (3 * (S + 1) ^ 2) ^ S * S : ℕ) * 2⁻¹ ^ 2 ^ n :=
  (prob_computableDAG_le n S).trans
    (mul_le_mul_right' (by exact_mod_cast card_computable_dag_le n S) _)

end Steps

/-- The same bound for a uniformly random function, as a probability under the uniform
distribution on the `2 ^ 2ⁿ` Boolean functions on `n` bits.  [AB09, p. 115]

**Proof sketch.** This is the book's route: by the union bound over the circuits
(`prob_computableDAG_le`, from step (ii) `prob_computes`), the probability is at most the
number of computable functions times `2 ^ (-2ⁿ)`, which is the fraction bounded by
`computableDAG_shannon_fraction_le`. -/
theorem prob_computableDAG_shannon_le (n : ℕ) :
    (PMF.uniformOfFintype ((Fin n → Bool) → Bool)).toOuterMeasure
        (computableDAG n (2 ^ n / (10 * n))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(2 ^ n : ℝ) / 10)) := by
  set A := computableDAG n (2 ^ n / (10 * n))
  calc _ ≤ (A.ncard : ENNReal) * 2⁻¹ ^ 2 ^ n := prob_computableDAG_le n _
    _ = ENNReal.ofReal ((A.ncard : ℝ) / 2 ^ 2 ^ n) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ← ENNReal.inv_pow, ← div_eq_mul_inv]
        simp [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(2 ^ n : ℝ) / 10)) :=
        ENNReal.ofReal_le_ofReal (computableDAG_shannon_fraction_le n)

/-- Reading the book's cutoff `2ⁿ/(10n)` as a real number changes nothing: a circuit has
size at most the real number `2ⁿ/(10n)` iff it has size at most `⌊2ⁿ/(10n)⌋` (at `n = 0`
both cutoffs are `0`). -/
theorem computableDAG_real_cutoff (n : ℕ) :
    {f : (Fin n → Bool) → Bool | ∃ C : DAGCircuit n, C.IsFaninTwo ∧
        (C.size : ℝ) ≤ (2 : ℝ) ^ n / (10 * n) ∧ C.eval = f} =
      computableDAG n (2 ^ n / (10 * n)) := by
  have key : ∀ k : ℕ, (k : ℝ) ≤ (2 : ℝ) ^ n / (10 * n) ↔ k ≤ 2 ^ n / (10 * n) := by
    intro k
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hpos : (0 : ℝ) < 10 * n := by positivity
      rw [le_div_iff₀ hpos, Nat.le_div_iff_mul_le (by omega)]
      constructor
      · intro h; exact_mod_cast (show ((k * (10 * n) : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) by
          push_cast; linarith)
      · intro h
        have : ((k * (10 * n) : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at this; linarith
  ext f
  simp only [Set.mem_setOf_eq, computableDAG, key]

end BoolCircuit
