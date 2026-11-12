/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.LupanovGates

/-!
# Every Boolean function has a fan-in-two circuit of size `O(2ⁿ / n)`

[AB09, p. 108]: "Claim 2.13 shows that every function `f` from `{0,1}ⁿ` to `{0,1}` can be
computed by a Boolean circuit of size `n2ⁿ`.  In fact, Exercise 6.1 shows that size
`O(2ⁿ/n)` also suffices."  This file proves the `O(2ⁿ/n)` bound in the book's model
`BoolCircuit.DAGCircuit` with fan-in two, with the explicit constant `40`:
`(n + 1) · size ≤ 40 · 2ⁿ`.

The circuit (built in `LupanovGates.lean`) splits the input into `y` (the first
`m = n - k` bits) and `z` (the last `k` bits), with `k = ⌊log₂ n⌋ - 1`, so `2ᵏ ≈ n / 2`:

1. the `2ᵐ` minterms of `y` and the `2ᵏ` minterms of `z`, each family by a prefix-sharing
   heap of fan-in-two `∧` gates (`2ᵐ⁺¹ - 1`, resp. `2ᵏ⁺¹ - 1` gates);
2. all `2^(2ᵏ)` functions of `z`, each one gate from a previous one (`g ∨ minterm`);
3. one `∧` gate per `y`-minterm `a`, with the `z`-function `f(a, ·)`, and a balanced
   `∨`-tree over these `2ᵐ` gates.

The total is at most `2n + 4·2ᵐ + 2·2ᵏ + 2^(2ᵏ)` vertices; `2ᵐ = 2ⁿ / 2ᵏ ≤ 4·2ⁿ/(n + 1)`, and
`2^(2ᵏ)` is small (`s · 2ˢ ≤ 2 · 2ⁿ` with `s = 2ᵏ`, the case split in `lupanov_arith`), give the
bound.

## Main definitions

* `BoolCircuit.Lupanov.lupDAG` — the circuit for `f` with `z`-width `k`.

## Main results

* `BoolCircuit.Lupanov.any_comb` — the `∨` of the combining gates is `f x`.
* `BoolCircuit.Lupanov.lupDAG_eval`, `lupDAG_isFaninTwo`, `lupDAG_size_le` — the circuit
  computes `f`, has fan-in two and at most `2n + 4·2^(n-k) + 2·2ᵏ + 2^(2ᵏ)` vertices.
* `BoolCircuit.exists_dagCircuit_faninTwo_mul_size_le` — every `f : {0,1}ⁿ → {0,1}` has a
  fan-in-two circuit with `(n + 1) · size ≤ 40 · 2ⁿ` ([AB09, p. 108, Ex 6.1]).
* `BoolCircuit.exists_dagCircuit_faninTwo_size_le_div` — the same as
  `size ≤ 40 · 2ⁿ / (n + 1)`.
* `Language.inSIZE_forty_two_pow_div` — every language is in `SIZE(40 · 2ⁿ / (n + 1))`.

## Divergences from [AB09]

* **Explicit constant.**  The book's `O(2ⁿ/n)` is stated with the explicit constant `40`
  and the denominator `n + 1` (so that the bound is meaningful, and true, at `n = 0`).
  The constant is not optimized; Lupanov's sharp `(1 + o(1)) 2ⁿ / n` is not attempted.
* **Sizes count inputs** ([AB09, Def 6.1]), which costs nothing asymptotically.
* **Construction.**  [AB09, Ex 6.1] leaves the construction to the reader; we use the
  standard split into all functions of the last `≈ log₂ n - 1` variables, shared, and
  the minterms of the remaining ones (Shannon's / Lupanov's argument).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, p. 108; Exercise 6.1.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

namespace Lupanov

variable {n : ℕ}

/-- Decoding the two heap paths of `x` gives back `x`. -/
theorem assemble_heapPath (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool) :
    assemble n k (heapPath x 0 (n - k) - 2 ^ (n - k)) (heapPath x (n - k) k - 2 ^ k) = x := by
  have hy := heapPath_bounds x 0 (n - k)
  have hz := heapPath_bounds x (n - k) k
  funext i
  unfold assemble
  split_ifs with hi
  · rw [show 2 ^ (n - k) + (heapPath x 0 (n - k) - 2 ^ (n - k)) = heapPath x 0 (n - k) by
      omega, testBit_heapPath x 0 (n - k) i hi, xget, dif_pos (by omega)]
    simp
  · rw [show 2 ^ k + (heapPath x (n - k) k - 2 ^ k) = heapPath x (n - k) k by omega,
      testBit_heapPath x (n - k) k (i - (n - k)) (by omega), xget, dif_pos (by omega)]
    congr 1; ext; simp; omega

/-- The `∨` of the combining gates is `f x`.

**Proof sketch.** Let `p₀`, `r₀` be the indices of the `y`- and `z`-parts of `x` (heap
paths minus the leading bit).  Combining gate `p` is true iff `p = p₀` and bit `r₀` of
`code p` is set, so the `∨` is bit `r₀` of `code p₀`, which by `testBit_ofBits` is
`f (assemble p₀ r₀) = f x` (`assemble_heapPath`). -/
theorem any_comb (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool) :
    (combRoots n k).any (vertexValue (gates f k) x) = f x := by
  have hy := heapPath_bounds x 0 (n - k)
  have hz := heapPath_bounds x (n - k) k
  rw [pow_succ] at hy hz
  set p0 := heapPath x 0 (n - k) - 2 ^ (n - k) with hp0
  set r0 := heapPath x (n - k) k - 2 ^ k with hr0
  have hcode : (code f k p0).testBit r0 = f x := by
    rw [code, testBit_ofBits]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [hr0, hp0, assemble_heapPath k hk x]
  rw [Bool.eq_iff_iff, ← hcode]
  simp only [combRoots, List.any_map, List.any_eq_true, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨p, hp, h⟩
    rw [value_comb f k hk x hp] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    rwa [show p = p0 by omega] at h2
  · intro h
    refine ⟨p0, by omega, ?_⟩
    rw [value_comb f k hk x (by omega)]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, h⟩

/-- `lupGates` meets the specification of a balanced `∨`-tree over the combining gates. -/
theorem lupGates_spec (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) :
    TreeSpec n .or (combRoots n k) (gates f k) (lupGates f k) := by
  refine emitTree_spec .or (by decide) _ _ (gates_acyclic f k hk) ?_
  intro v hv
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  simp only [combRoots, List.mem_map, List.mem_range] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  rw [length_gates]
  omega

/-- The `O(2ⁿ/n)` circuit for `f` with `z`-width `k ≤ n`: `n` negations, the minterm heaps
of `y` (the first `n - k` inputs) and `z` (the last `k`), the table of all functions of
`z`, one combining `∧` gate per `y`-minterm, and a balanced `∨`-tree on top.
[AB09, Ex 6.1] -/
def lupDAG (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) : DAGCircuit n where
  gates := (lupGates f k).1
  output := (lupGates f k).2
  args_lt := (lupGates_spec f k hk).acyclic
  output_lt := (lupGates_spec f k hk).vertex_lt

/-- `lupDAG f k` computes `f`.

**Proof sketch.** The output `∨`-tree computes the `∨` of the combining gates.  On input
`x = (y, z)` exactly one `y`-minterm is true (the one indexed by `y`'s heap path), so the
`∨` is the value of the `z`-function table entry `f(y, ·)` at `z`, which is `f x`
(`any_comb`). -/
theorem lupDAG_eval (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) (x : Fin n → Bool) :
    (lupDAG f k hk).eval x = f x := by
  have h := (lupGates_spec f k hk).value x
  change vertexValue (lupGates f k).1 x (lupGates f k).2 = f x
  rw [h, ← any_comb f k hk x]
  rfl

/-- `lupDAG f k` has fan-in two. -/
theorem lupDAG_isFaninTwo (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) :
    (lupDAG f k hk).IsFaninTwo := by
  have hs := lupGates_spec f k hk
  obtain ⟨e, he⟩ := hs.extends_gates
  have key : ∀ g ∈ (lupGates f k).1, g.FaninTwo := by
    intro g hg
    rw [he, List.mem_append] at hg
    rcases hg with hg | hg
    · simp only [gates, List.mem_map, List.mem_range] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      exact gateAt_faninTwo f k hk j hj
    · obtain ⟨hkd, hnd, hl⟩ := hs.new_gates g (by rw [he, List.drop_left]; exact hg)
      exact ⟨⟨hnd, fun h => absurd (hkd ▸ h) (by decide)⟩, hl⟩
  exact ⟨fun g hg => (key g hg).1, fun g hg => (key g hg).2⟩

/-- `lupDAG f k` has at most `2n + 4·2^(n-k) + 2·2ᵏ + 2^(2ᵏ)` vertices: `n` inputs, `n`
negations, `2^(n-k+1) - 1` and `2^(k+1) - 1` heap nodes, `2^(2ᵏ)` table gates,
`2^(n-k)` combining gates and `2^(n-k) - 1` gates in the `∨`-tree. -/
theorem lupDAG_size_le (f : (Fin n → Bool) → Bool) (k : ℕ) (hk : k ≤ n) :
    (lupDAG f k hk).size ≤ 2 * n + 4 * 2 ^ (n - k) + 2 * 2 ^ k + 2 ^ 2 ^ k := by
  have hl := (lupGates_spec f k hk).length_le
  obtain ⟨o1, o2, o3, o4, p1, p2, p3⟩ := offsets n k
  have ht : treeCost (combRoots n k).length = 2 ^ (n - k) - 1 := by
    simp only [combRoots, List.length_map, List.length_range, treeCost]
    rw [if_neg (by omega)]
  rw [ht, length_gates] at hl
  change n + (lupGates f k).1.length ≤ _
  omega

end Lupanov

/-! ## The size bound -/

variable {n : ℕ}

/-- `(n + 1)² ≤ 4 · 2ⁿ`. -/
private theorem succ_sq_le_four_mul_two_pow (n : ℕ) : (n + 1) * (n + 1) ≤ 4 * 2 ^ n := by
  rcases (by omega : n < 2 ∨ 2 ≤ n) with h | h
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> norm_num
  · induction n, h using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rw [pow_succ]
      nlinarith

/-- With `k = ⌊log₂ n⌋ - 1`: `(n + 1)(2n + 4·2^(n-k) + 2·2ᵏ + 2^(2ᵏ)) ≤ 40 · 2ⁿ`.

**Proof sketch.** Write `s = 2ᵏ` and `M = 2^(n-k)`, so `M s = 2ⁿ`.  Since
`n < 2^(⌊log₂ n⌋ + 1)`, `n + 1 ≤ 4s`; since `2^⌊log₂ n⌋ ≤ n`, `s ≤ n + 1`; and either
`n ≤ 1` and `s = 1`, or `2s ≤ n`, whence `s · 2ˢ ≤ 2ˢ · 2ˢ ≤ 2ⁿ`; in all cases
`s · 2ˢ ≤ 2 · 2ⁿ`.  With `(n + 1)² ≤ 4 · 2ⁿ` the four terms are at most `8 · 2ⁿ`
(`2n(n + 1)`), `16 · 2ⁿ` (`4(n + 1)M ≤ 16 s M`), `8 · 2ⁿ` (`2(n + 1)s`) and `8 · 2ⁿ`
(`(n + 1)2ˢ ≤ 4 s 2ˢ`). -/
theorem lupanov_arith (n : ℕ) :
    (n + 1) * (2 * n + 4 * 2 ^ (n - (Nat.log 2 n - 1)) + 2 * 2 ^ (Nat.log 2 n - 1) +
      2 ^ 2 ^ (Nat.log 2 n - 1)) ≤ 40 * 2 ^ n := by
  set L := Nat.log 2 n with hL
  set k := L - 1 with hkdef
  set s := 2 ^ k with hs
  set M := 2 ^ (n - k) with hM
  have hLn : L ≤ n := Nat.log_le_self 2 n
  have hMs : M * s = 2 ^ n := by rw [hM, hs, ← pow_add]; congr 1; omega
  have hn1 : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hs1 : 1 ≤ s := Nat.one_le_two_pow
  -- `n + 1 ≤ 4s` and `s ≤ n + 1`
  have hb : n + 1 ≤ 4 * s := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · rw [h0] at hn1; simp at hn1; omega
    · have : 2 ^ (L + 1) = 4 * s := by
        rw [hs, show L + 1 = k + 2 by omega, pow_add]; ring
      omega
  have hc : s ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp [hs, hkdef, hL]
    · have h1 : s ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ L ≤ n := Nat.pow_log_le_self 2 h0.ne'
      omega
  -- `s · 2ˢ ≤ 2 · 2ⁿ`
  have hd : s * 2 ^ s ≤ 2 * 2 ^ n := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · have : s = 1 := by rw [hs, hkdef, h0]; rfl
      rw [this]
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    · have h2 : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by
        rintro rfl; simp [hL] at h0)
      have h3 : 2 ^ L = 2 * s := by
        rw [hs, show L = k + 1 by omega, pow_succ]; ring
      have h4 : s ≤ 2 ^ s := (Nat.lt_two_pow_self).le
      calc s * 2 ^ s ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_right _ h4
        _ = 2 ^ (s + s) := (pow_add 2 s s).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 2 * 2 ^ n := by omega
  have he := succ_sq_le_four_mul_two_pow n
  have a1 : (n + 1) * M ≤ 4 * s * M := Nat.mul_le_mul_right _ hb
  have a2 : (n + 1) * s ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_left _ hc
  have a3 : (n + 1) * 2 ^ s ≤ 4 * s * 2 ^ s := Nat.mul_le_mul_right _ hb
  have a4 : n * (n + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right _ (Nat.le_succ n)
  nlinarith

/-- Every Boolean function on `n` bits is computed by a fan-in-two circuit of the book's
model whose size `S` satisfies `(n + 1) · S ≤ 40 · 2ⁿ`, i.e. `S = O(2ⁿ / n)`.
[AB09, p. 108] ("Exercise 6.1 shows that size `O(2ⁿ/n)` also suffices"), [AB09, Ex 6.1].

The book's `O(2ⁿ/n)` is made explicit: constant `40`, denominator `n + 1` (so the bound
is also meaningful at `n = 0`), and the size counts the `n` input vertices
([AB09, Def 6.1]).

**Proof sketch.** Take `k = ⌊log₂ n⌋ - 1` and the circuit `lupDAG f k` (split `x = (y, z)`
with `|z| = k`; all `2^(2ᵏ)` functions of `z` and all `2^(n-k)` minterms of `y`, shared;
`f(x) = ⋁_a (minterm_a(y) ∧ f(a, ·)(z))`).  It computes `f` and has fan-in two; its size
is at most `2n + 4·2^(n-k) + 2·2ᵏ + 2^(2ᵏ)`, and `lupanov_arith` bounds `n + 1` times
this by `40 · 2ⁿ`. -/
theorem exists_dagCircuit_faninTwo_mul_size_le (f : (Fin n → Bool) → Bool) :
    ∃ C : DAGCircuit n, C.IsFaninTwo ∧ (∀ x, C.eval x = f x) ∧
      (n + 1) * C.size ≤ 40 * 2 ^ n := by
  have hk : Nat.log 2 n - 1 ≤ n := by have := Nat.log_le_self 2 n; omega
  refine ⟨Lupanov.lupDAG f _ hk, Lupanov.lupDAG_isFaninTwo f _ hk,
    Lupanov.lupDAG_eval f _ hk, ?_⟩
  exact (Nat.mul_le_mul_left _ (Lupanov.lupDAG_size_le f _ hk)).trans (lupanov_arith n)

/-- Every Boolean function on `n` bits is computed by a fan-in-two circuit of the book's
model of size at most `40 · 2ⁿ / (n + 1)` (natural-number division): the `O(2ⁿ/n)` bound
of [AB09, p. 108, Ex 6.1] with an explicit constant (see
`exists_dagCircuit_faninTwo_mul_size_le`). -/
theorem exists_dagCircuit_faninTwo_size_le_div (f : (Fin n → Bool) → Bool) :
    ∃ C : DAGCircuit n, C.IsFaninTwo ∧ (∀ x, C.eval x = f x) ∧
      C.size ≤ 40 * 2 ^ n / (n + 1) := by
  obtain ⟨C, h1, h2, h3⟩ := exists_dagCircuit_faninTwo_mul_size_le f
  exact ⟨C, h1, h2, (Nat.le_div_iff_mul_le (Nat.succ_pos n)).mpr (by rw [mul_comm]; exact h3)⟩

end BoolCircuit

/-- Every language `L ⊆ {0,1}*` is in `SIZE(40 · 2ⁿ / (n + 1))`: at each length `n`, the
restriction of `L` to `{0,1}ⁿ` is a Boolean function, which has a fan-in-two circuit of
that size.  [AB09, p. 108, Ex 6.1] -/
theorem Language.inSIZE_forty_two_pow_div (L : Language Bool) :
    L.InSIZE (fun n => 40 * 2 ^ n / (n + 1)) := by
  classical
  let F : ∀ n, (Fin n → Bool) → Bool := fun n x => decide (List.ofFn x ∈ L)
  let C : BoolCircuit.DAGCircuitFamily :=
    ⟨fun n => Classical.choose (BoolCircuit.exists_dagCircuit_faninTwo_size_le_div (F n))⟩
  have hC : ∀ n, (C.circuit n).IsFaninTwo ∧ (∀ x, (C.circuit n).eval x = F n x) ∧
      (C.circuit n).size ≤ 40 * 2 ^ n / (n + 1) := fun n =>
    Classical.choose_spec (BoolCircuit.exists_dagCircuit_faninTwo_size_le_div (F n))
  refine ⟨C, fun n => (hC n).1, fun n => (hC n).2.2, ?_⟩
  ext w
  rw [BoolCircuit.DAGCircuitFamily.mem_language_iff, (hC w.length).2.1]
  simp [F, List.ofFn_get]
