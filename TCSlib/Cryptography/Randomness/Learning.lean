/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.LearningTheory.PAC
import TCSlib.Cryptography.Asymptotic.PRF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandom functions make an unlearnable concept class (statement phase)

[PS10, §8.1, Theorem 179.1]: if pseudorandom functions exist, there is a p.p.t.-decidable concept
class that no non-uniform p.p.t. learner can learn: given polynomially many labelled uniform
examples, it predicts the label of a fresh uniform point with probability at most `½` plus a
negligible amount.

**The class.** For a PRF family `{f_k}`, `C_k = {x : f_k(x)₁ = 1}`, the first output bit
(`prfConcept`).

**The learner.** An efficient learner is a machine `A` run at parameter `n` on
`⟨labelled sample, x⟩`. Its hypothesis on `x` is whether it outputs `[true]` (`learnerOf`). The
examples are given non-adaptively, as in the source's question. The prediction game and the PAC
notions are those of the information-theoretic layer `TCSlib.LearningTheory.PAC` (S3d layer 1,
[Shilun-Allan-Li/tcslib#194]), at the uniform distribution on `{0,1}^n` and uniform keys.

## Main definitions

* `Randomness.prfConcept`, `Randomness.encodeSample`, `Randomness.learnerOf`.

## Main results

* `Randomness.prfConcept_decidable` (Thm 179.1, part (a), proved): membership is
  polynomial-time decidable given the key.
* `Randomness.predictAdv_prfConcept_negligible` (Thm 179.1, part (b), stated; a `sorry` under the
  source's sketch): every efficient learner's prediction advantage is negligible.
* `Randomness.not_weakLearnsUnder_prfConcept` (Thm 179.1, part (c), proved from (b) and the PAC
  layer's bridge): no efficient learner weakly PAC-learns the class under the uniform distribution
  with a constant edge.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §8.1, Theorem 179.1 (book p. 179).
-/

namespace TCSlib.Cryptography.Randomness

open Complexity Turing TCSlib.Cryptography TCSlib.LearningTheory.PAC TCSlib.InformationTheory

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))

/-- **The concept class of Theorem 179.1** at parameter `n`: `C_k(x) = f_k(x)₁`, the first output
bit (`false` at `n = 0`). -/
def prfConcept (n : ℕ) (k x : Fin n → Bool) : Bool := (List.ofFn (F n k x)).headD false

/-- The encoding of a labelled sample for a learner machine: the nested pairs of `⟨x_j, [b_j]⟩`. -/
def encodeSample {n m : ℕ} (S : Fin m → (Fin n → Bool) × Bool) : List Bool :=
  (List.ofFn fun j => pairEncode (List.ofFn (S j).1) [(S j).2]).foldr pairEncode []

/-- **The learner of a machine** `A` at parameter `n` with `m` examples: on the labelled sample `S`
and coins `r`, the hypothesis `x ↦ [A(1^n, ⟨S, x⟩; r) = [true]]`. -/
def learnerOf (A : NUPPT) (n m : ℕ) :
    (Fin m → (Fin n → Bool) × Bool) → A.Coins n → (Fin n → Bool) → Bool :=
  fun S r x => decide (A.runAt n (pairEncode (encodeSample S) (List.ofFn x)) r = [true])

/-- **Theorem 179.1 (a): the class is p.p.t.-decidable** given the key: the first bit of the PRF's
evaluator decides membership. -/
theorem prfConcept_decidable (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ n (k x : Fin n → Bool), f (pairEncode (List.ofFn k) (List.ofFn x)) = [prfConcept F n k x] :=
  ⟨fun z => [(E z).headD false], polyTimeComputable_headD.comp hE, fun n k x => by
    simp only [prfConcept, hFE]⟩

/-- **Theorem 179.1 (b): no efficient learner predicts the class** [PS10, Theorem 179.1]: if `F` is
a PRF, then for every non-uniform PPT learner `A` and polynomial number `m` of examples, the
prediction advantage `|Pr[A predicts C_k(x)] − ½|` at uniform `k`, uniform examples and a fresh
uniform `x` is negligible.

**Proof sketch** (the source's, made explicit).
1. The distinguisher `D` against the PRF draws `m(n) + 1` uniform points, queries its oracle at
   them, labels the first `m(n)` with the answers' first bits, runs `A` on the labelled sample and
   the last point, and outputs whether `A`'s prediction equals the last answer's first bit. With
   `f_k` this is the prediction game. `D` is a machine by T1 (non-adaptive queries).
2. With a random function, the last point's label is a uniform bit independent of the sample,
   unless the last point was sampled, with probability at most `m(n)/2^n`. So `D` accepts with
   probability at most `½ + m(n)/2^n`, and at least `½ − m(n)/2^n`.
3. Hence the advantage is at most the PRF advantage plus `m(n)/2^n`: negligible. -/
theorem predictAdv_prfConcept_negligible (hF : PRF F) (A : NUPPT) (m : PolyExpr) :
    Negligible fun n => predictAdv (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) := by
  sorry

/-- **Theorem 179.1 (c): no efficient weak PAC learner** under the uniform distribution: for edges
`δ < γ ≤ ½`, every efficient learner fails to `(γ, δ)`-weakly learn the class from some
parameter on. Proved from part (b) and the PAC layer's `not_weakLearnsUnder_of_predictAdv_le`. -/
theorem not_weakLearnsUnder_prfConcept (hF : PRF F) (A : NUPPT) (m : PolyExpr) {γ δ : ℝ}
    (hδγ : δ < γ) (hγ : γ ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ¬ WeakLearnsUnder (FinDist.uniform (Fin n → Bool)) (prfConcept F n)
      (m.eval n) (learnerOf A n (m.eval n)) γ δ := by
  obtain ⟨n₁, hn₁⟩ := predictAdv_prfConcept_negligible F hF A m 1
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (2 / (γ - δ))
  refine ⟨max n₁ (n₂ + 1), fun n hn => ?_⟩
  have h1 := hn₁ n (le_trans (le_max_left _ _) hn)
  have hpos : (0 : ℝ) < γ - δ := by linarith
  have hn' : (n₂ : ℝ) + 1 ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by linarith [(Nat.cast_nonneg n₂ : (0 : ℝ) ≤ n₂)]
  have hsmall : 1 / (n : ℝ) ^ 1 ≤ (γ - δ) / 2 := by
    rw [pow_one, div_le_div_iff₀ hnpos (by norm_num)]
    have : 2 / (γ - δ) < n := by linarith
    rw [div_lt_iff₀ hpos] at this
    linarith
  have hadv : predictAdv (prfConcept F n) (m.eval n) (learnerOf A n (m.eval n)) ≤ (γ - δ) / 2 :=
    le_trans (le_abs_self _) (le_trans h1.le hsmall)
  exact not_weakLearnsUnder_of_predictAdv_le hadv (by linarith) hγ

end TCSlib.Cryptography.Randomness
