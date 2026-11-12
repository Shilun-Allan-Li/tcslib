/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import TCSlib.Complexity.Randomized.AlgCircuit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A small circuit with exponentially many monomials

[AB09, §7.2.3, p.129]: "the polynomial `∏ᵢ (1 + xᵢ)` can be computed using a circuit of size
`2n` but has `2ⁿ` terms if we open all parentheses." This is why `ZEROP` is not decided by
expanding the polynomial.

## Main definitions

* `Randomized.AlgGate.isOp` — the node is an operator (`+`, `−` or `×`).
* `Randomized.AlgCircuit.prodOnePlus` — the circuit for `∏_{i<n} (1 + xᵢ)`.

## Main results

* `Randomized.AlgCircuit.wellFormed_prodOnePlus` — it is a well-formed circuit.
* `Randomized.AlgCircuit.countP_isOp_prodOnePlus` — it has exactly `2n` operator nodes.
* `Randomized.AlgCircuit.size_prodOnePlus` — it has `3n + 1` nodes in all.
* `Randomized.AlgCircuit.toMvPolynomial_prodOnePlus` — it computes `∏ᵢ (1 + Xᵢ)`.
* `Randomized.AlgCircuit.card_support_prod_one_add_X` — that polynomial has `2ⁿ` monomials.

## Divergences

* `AlgCircuit.size` counts every node, including the `n` input nodes and the constant `1`;
  the book's `2n` counts the `n` additions and `n` multiplications. We prove both counts:
  `2n` operator nodes, `3n + 1` nodes in all.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open MvPolynomial

namespace AlgGate

variable {n : ℕ}

/-- The node is an operator `+`, `−` or `×` (not an input or the constant). -/
def isOp : AlgGate n → Bool
  | add _ _ => true
  | sub _ _ => true
  | mul _ _ => true
  | _ => false

end AlgGate

namespace AlgCircuit

variable {n : ℕ}

/-- The input node `xᵢ` for `i < n` (the constant `1` past the inputs; never used). -/
def varOrOne (i : ℕ) : AlgGate n := if h : i < n then .var ⟨i, h⟩ else .one

/-- The nodes of the product circuit after `k` factors: node `0` is `1`, and factor `i`
adds `xᵢ` (node `3i+1`), `1 + xᵢ` (node `3i+2`) and the running product (node `3i+3`). -/
def prodOnePlusGates : ℕ → List (AlgGate n)
  | 0 => [.one]
  | k + 1 => prodOnePlusGates k ++ [varOrOne k, .add 0 (3 * k + 1), .mul (3 * k) (3 * k + 2)]

/-- The circuit computing `∏_{i<n} (1 + xᵢ)`.  [AB09, §7.2.3, p.129] -/
def prodOnePlus (n : ℕ) : AlgCircuit n := ⟨prodOnePlusGates n⟩

/-- `k` factors take `3k + 1` nodes. -/
theorem length_prodOnePlusGates (k : ℕ) : (prodOnePlusGates (n := n) k).length = 3 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [prodOnePlusGates, ih]; ring

/-- `k` factors take `2k` operator nodes. -/
theorem countP_isOp_prodOnePlusGates (k : ℕ) :
    (prodOnePlusGates (n := n) k).countP AlgGate.isOp = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hv : (varOrOne (n := n) k).isOp = false := by
      unfold varOrOne; split <;> rfl
    simp only [prodOnePlusGates, List.countP_append, ih, List.countP_cons, List.countP_nil, hv]
    simp [AlgGate.isOp]
    ring

/-- Every node of the product circuit reads earlier nodes only.

**Proof sketch.** Induction on `k`; the three new nodes read `0`, `3k`, `3k+1`, `3k+2`. -/
theorem refsBelow_prodOnePlusGates (k i : ℕ) (h : i < (prodOnePlusGates (n := n) k).length) :
    ((prodOnePlusGates k)[i]).refsBelow i = true := by
  induction k with
  | zero =>
    simp only [prodOnePlusGates, List.length_singleton, Nat.lt_one_iff] at h
    subst h
    rfl
  | succ k ih =>
    simp only [prodOnePlusGates]
    by_cases hi : i < (prodOnePlusGates (n := n) k).length
    · rw [List.getElem_append_left hi]
      exact ih hi
    · rw [length_prodOnePlusGates] at hi
      simp only [prodOnePlusGates, List.length_append, length_prodOnePlusGates,
        List.length_cons, List.length_nil] at h
      obtain ⟨j, rfl⟩ : ∃ j, i = 3 * k + 1 + j := ⟨i - (3 * k + 1), by omega⟩
      rw [List.getElem_append, dif_neg (by rw [length_prodOnePlusGates]; omega)]
      simp only [length_prodOnePlusGates, Nat.add_sub_cancel_left]
      obtain _ | _ | _ | j := j
      · simp only [List.getElem_cons_zero, varOrOne]
        split <;> rfl
      · simp [AlgGate.refsBelow]
      · simp [AlgGate.refsBelow]; omega
      · omega

/-- **The product circuit is well formed.** -/
theorem wellFormed_prodOnePlus : (prodOnePlus n).WellFormed := by
  refine ⟨?_, fun i h => refsBelow_prodOnePlusGates n i h⟩
  rw [← List.length_pos_iff]
  simp [prodOnePlus, length_prodOnePlusGates]

/-- **The product circuit has `2n` operator nodes** — the book's size `2n`.
[AB09, §7.2.3, p.129] -/
theorem countP_isOp_prodOnePlus : (prodOnePlus n).gates.countP AlgGate.isOp = 2 * n :=
  countP_isOp_prodOnePlusGates n

/-- The product circuit has `3n + 1` nodes: `2n` operators, `n` inputs and the constant `1`. -/
theorem size_prodOnePlus : (prodOnePlus n).size = 3 * n + 1 :=
  length_prodOnePlusGates n

/-- Reading the last entry of `vs ++ [v]`. -/
private theorem getD_append_singleton_length {R : Type*} [Zero R] (vs : List R) (v : R) :
    (vs ++ [v]).getD vs.length 0 = v := by
  simp

/-- After `k` factors, node `0` holds `1` and node `3k` holds `∏_{i<k} (1 + xᵢ)` (the input
read is `1` past `n`).

**Proof sketch.** Induction on `k`. The three new nodes read `xₖ`, then node `0` and the new
`xₖ`, then node `3k` and the new `1 + xₖ`; all earlier entries are unchanged by appending. -/
theorem run_prodOnePlusGates {R : Type*} [CommRing R] (x : Fin n → R) (k : ℕ) :
    (run x (prodOnePlusGates k)).getD 0 0 = 1 ∧
      (run x (prodOnePlusGates k)).getD (3 * k) 0 =
        ∏ i ∈ Finset.range k, (1 + (varOrOne i : AlgGate n).eval x []) := by
  induction k with
  | zero => simp [prodOnePlusGates, run, AlgGate.eval]
  | succ k ih =>
    obtain ⟨h0, hk⟩ := ih
    set vs := run x (prodOnePlusGates (n := n) k) with hvs
    have hlen : vs.length = 3 * k + 1 := by rw [hvs, length_run, length_prodOnePlusGates]
    have hg : prodOnePlusGates (n := n) (k + 1) = prodOnePlusGates k ++ [varOrOne k] ++
        [.add 0 (3 * k + 1)] ++ [.mul (3 * k) (3 * k + 2)] := by
      simp [prodOnePlusGates]
    have hx : ∀ ws : List R, (varOrOne (n := n) k).eval x ws = (varOrOne (n := n) k).eval x [] :=
      fun ws => by unfold varOrOne; split <;> rfl
    rw [hg, run_append_singleton, run_append_singleton, run_append_singleton, ← hvs]
    set v1 := vs ++ [(varOrOne (n := n) k).eval x vs]
    have h1len : v1.length = 3 * k + 2 := by simp [v1, hlen]
    set v2 := v1 ++ [(AlgGate.add (n := n) 0 (3 * k + 1)).eval x v1]
    have h2len : v2.length = 3 * k + 3 := by simp [v2, h1len]
    have e10 : v1.getD 0 0 = 1 := by rw [List.getD_append _ _ _ _ (by omega), h0]
    have e1k : v1.getD (3 * k) 0 = vs.getD (3 * k) 0 := List.getD_append _ _ _ _ (by omega)
    have e1x : v1.getD (3 * k + 1) 0 = (varOrOne (n := n) k).eval x [] := by
      rw [← hlen, getD_append_singleton_length, hx]
    have e20 : v2.getD 0 0 = 1 := by rw [List.getD_append _ _ _ _ (by omega), e10]
    have e2k : v2.getD (3 * k) 0 = vs.getD (3 * k) 0 := by
      rw [List.getD_append _ _ _ _ (by omega), e1k]
    have e2x : v2.getD (3 * k + 2) 0 = 1 + (varOrOne (n := n) k).eval x [] := by
      rw [← h1len, getD_append_singleton_length]
      simp only [AlgGate.eval, e10, e1x]
    refine ⟨by rw [List.getD_append _ _ _ _ (by omega), e20], ?_⟩
    rw [show 3 * (k + 1) = v2.length by omega, getD_append_singleton_length]
    simp only [AlgGate.eval, e2k, e2x, hk, Finset.prod_range_succ]

/-- **The product circuit computes `∏ᵢ (1 + Xᵢ)`.**  [AB09, §7.2.3, p.129] -/
theorem toMvPolynomial_prodOnePlus :
    (prodOnePlus n).toMvPolynomial = ∏ i : Fin n, (1 + X i) := by
  have h := (run_prodOnePlusGates (n := n) (X : Fin n → MvPolynomial (Fin n) ℤ) n).2
  rw [toMvPolynomial, eval, size_prodOnePlus, Nat.add_sub_cancel]
  refine h.trans ?_
  rw [← Fin.prod_univ_eq_prod_range (fun i => 1 + (varOrOne i : AlgGate n).eval X [])]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [varOrOne, AlgGate.eval]

/-- **`∏ᵢ (1 + Xᵢ)` has `2ⁿ` monomials** [AB09, §7.2.3, p.129]: opening the parentheses gives
one monomial `∏_{i ∈ t} Xᵢ` for each subset `t`, all distinct.

**Proof sketch.** `Finset.prod_one_add` gives one monomial per subset `t`, with exponent
`∑_{i∈t} eᵢ`; this exponent map is injective, so the supports are disjoint singletons. -/
theorem card_support_prod_one_add_X :
    (∏ i : Fin n, (1 + X i : MvPolynomial (Fin n) ℤ)).support.card = 2 ^ n := by
  classical
  let e : Finset (Fin n) → Fin n →₀ ℕ := fun t => ∑ i ∈ t, Finsupp.single i 1
  have he : ∀ t i, e t i = if i ∈ t then 1 else 0 := fun t i => by
    simp only [e, Finsupp.finset_sum_apply, Finsupp.single_apply]
    simp [Finset.sum_ite_eq']
  have hinj : Function.Injective e := fun s t hst => by
    ext i
    have := he s i
    rw [hst, he t i] at this
    split_ifs at this <;> simp_all
  have hp : (∏ i : Fin n, (1 + X i : MvPolynomial (Fin n) ℤ)) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, monomial (e t) (1 : ℤ) := by
    rw [Finset.prod_one_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [monomial_sum_one]
    rfl
  have hs : ∀ t, Finsupp.support (monomial (e t) (1 : ℤ)) = {e t} := fun t =>
    Finsupp.support_single_ne_zero _ one_ne_zero
  rw [hp]
  unfold MvPolynomial.support
  rw [Finsupp.support_sum_eq_biUnion]
  · rw [Finset.card_biUnion]
    · simp [hs]
    · intro s _ t _ hst
      simpa [Function.onFun, hs] using (hinj.ne hst).symm
  · intro s t hst
    simpa [hs] using (hinj.ne hst).symm

/-- The circuit `prodOnePlus n` of size `3n + 1` (`2n` operators) computes a polynomial with
`2ⁿ` monomials.  [AB09, §7.2.3, p.129] -/
theorem card_support_toMvPolynomial_prodOnePlus :
    (prodOnePlus n).toMvPolynomial.support.card = 2 ^ n := by
  rw [toMvPolynomial_prodOnePlus, card_support_prod_one_add_X]

end AlgCircuit

end Randomized
