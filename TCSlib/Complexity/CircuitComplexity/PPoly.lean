/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuit

/-!
# `SIZE(T)` and `P/poly`

The circuit size classes of [AB09, Defs 6.2 and 6.5], over the book's circuit model
`BoolCircuit.DAGCircuit`: fan-in-two DAGs whose size counts every vertex, inputs included.

## Main definitions

* `Language.InSIZE` — [AB09, Def 6.2].
* `Language.InPPoly` — [AB09, Def 6.5], `P/poly = ⋃_c SIZE(n^c)`, in the repaired form
  `⋃_{a,k} SIZE(a(n + 1)^k)` (see the divergences).
* `BoolCircuit.PPoly` — the same class as a `Set (Language Bool)`.

## Main results

* `Language.InSIZE.mono`, `Language.InSIZE.inPPoly` — monotonicity, and polynomial
  `SIZE` classes lie in `P/poly`.
* `Language.inPPoly_iff` — `P/poly` membership as one family carrying its own size bound.
* `Language.inPPoly_iff_eventually` — `P/poly` is the literal `|C_n| ≤ n ^ c`, required only
  for `n ≥ 2`.
* `Language.not_inSIZE_pow`, `Language.setOf_inSIZE_pow_eq_empty` — the fully literal
  `⋃_c SIZE(n^c)` is empty; `BoolCircuit.DAGCircuit.eval_of_size_le_one` — a size-`1`
  circuit on one input is the identity.

The same class over the layered model of the Razborov–Smolensky development is
`Language.InLayeredPPoly`; `LayeredDAG.lean` proves the two coincide.

## Divergences from [AB09, Defs 6.2 and 6.5]

* The model's own divergences (fan-in at most two rather than exactly two, constants via
  fan-in-zero gates, a single output) are listed in `DAGCircuit.lean`.
* [AB09] writes `P/poly = ⋃_c SIZE(n^c)`; we write `∃ a k, SIZE(a * (n + 1) ^ k)`.  The
  literal union is **empty** (`Language.not_inSIZE_pow`, `Language.setOf_inSIZE_pow_eq_empty`):
  a circuit has at least one vertex (`BoolCircuit.DAGCircuit.one_le_size`), so `n ^ c` with
  `c ≥ 1` is violated at `n = 0`, and `n ^ 0 = 1` is violated at `n = 2` (two input
  vertices).  Even ignoring length `0`, length `1` would be restricted to size `1`, i.e. the
  identity circuit `x₀` (`BoolCircuit.DAGCircuit.eval_of_size_le_one`).  The repair changes
  only the finitely many lengths `n ≤ 1`: `Language.inPPoly_iff_eventually` shows that
  `P/poly` is exactly "`|C_n| ≤ n ^ c` for every `n ≥ 2`", with arbitrary circuits at
  `n ≤ 1`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Definitions 6.2 and 6.5.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- `L ∈ SIZE(T)`: some fan-in-two circuit family decides `L` with the length-`n` circuit
of size at most `T n`.  [AB09, Def 6.2] -/
def Language.InSIZE (T : ℕ → ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.DAGCircuitFamily,
    C.HasFaninTwo ∧ (∀ n, (C.circuit n).size ≤ T n) ∧ C.language = L

/-- `L ∈ P/poly`: some polynomial-size fan-in-two circuit family decides `L`.
[AB09, Def 6.5] -/
def Language.InPPoly (L : Language Bool) : Prop :=
  ∃ a k : ℕ, L.InSIZE (fun n => a * (n + 1) ^ k)

/-- `SIZE(T) ⊆ SIZE(T')` whenever `T ≤ T'` pointwise. -/
theorem Language.InSIZE.mono {T T' : ℕ → ℕ} {L : Language Bool} (hL : L.InSIZE T)
    (h : ∀ n, T n ≤ T' n) : L.InSIZE T' := by
  obtain ⟨C, hG, hS, hC⟩ := hL
  exact ⟨C, hG, fun n => (hS n).trans (h n), hC⟩

/-- A language in `SIZE(T)` for a polynomially bounded `T` is in `P/poly`. -/
theorem Language.InSIZE.inPPoly {T : ℕ → ℕ} {L : Language Bool} {a k : ℕ}
    (hL : L.InSIZE T) (hT : ∀ n, T n ≤ a * (n + 1) ^ k) : L.InPPoly :=
  ⟨a, k, hL.mono hT⟩

/-- `P/poly` membership as one family carrying its own size bound. -/
theorem Language.inPPoly_iff (L : Language Bool) :
    L.InPPoly ↔ ∃ C : BoolCircuit.DAGCircuitFamily,
      C.HasFaninTwo ∧ C.IsPolySize ∧ C.language = L := by
  constructor
  · rintro ⟨a, k, C, hG, hS, hL⟩
    exact ⟨C, hG, ⟨a, k, hS⟩, hL⟩
  · rintro ⟨C, hG, ⟨a, k, hS⟩, hL⟩
    exact ⟨a, k, C, hG, hS, hL⟩

/-- A circuit has at least one vertex: its output. -/
theorem BoolCircuit.DAGCircuit.one_le_size {n : ℕ} (C : BoolCircuit.DAGCircuit n) :
    1 ≤ C.size := by
  have := C.output_lt
  unfold BoolCircuit.DAGCircuit.size
  omega

/-- A circuit on one input with a single vertex computes the identity `x₀`: it has no gate,
so its output is the input vertex.  This is the only circuit the literal bound `n ^ c`
allows at length `1`. -/
theorem BoolCircuit.DAGCircuit.eval_of_size_le_one (C : BoolCircuit.DAGCircuit 1)
    (h : C.size ≤ 1) (x : Fin 1 → Bool) : C.eval x = x 0 := by
  have hg : C.gates.length = 0 := by unfold BoolCircuit.DAGCircuit.size at h; omega
  have ho : C.output = 0 := by have := C.output_lt; omega
  rw [BoolCircuit.DAGCircuit.eval, ho]
  exact C.values_getD_input x 0

/-- **The literal `SIZE(n^c)` is empty.**  No language has fan-in-two circuits of size at
most `n ^ c` at every length `n`: for `c ≥ 1` the bound is `0` at `n = 0`, and for `c = 0`
it is `1` at `n = 2`, while every circuit has at least one vertex and one on two inputs has
at least two.  This is why `Language.InPPoly` uses `a * (n + 1) ^ k` in place of [AB09,
Def 6.5]'s `n ^ c`. -/
theorem Language.not_inSIZE_pow (c : ℕ) (L : Language Bool) :
    ¬ L.InSIZE (fun n => n ^ c) := by
  rintro ⟨C, -, hS, -⟩
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have h2 := hS 2
    have : 2 ≤ (C.circuit 2).size := by unfold BoolCircuit.DAGCircuit.size; omega
    simp only [pow_zero] at h2
    omega
  · have h0 : (C.circuit 0).size ≤ 0 ^ c := hS 0
    have := (C.circuit 0).one_le_size
    rw [Nat.zero_pow hc] at h0
    omega

/-- The literal union `⋃_c SIZE(n^c)` of [AB09, Def 6.5] is empty. -/
theorem Language.setOf_inSIZE_pow_eq_empty :
    {L : Language Bool | ∃ c, L.InSIZE (fun n => n ^ c)} = ∅ := by
  ext L
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  exact fun c => Language.not_inSIZE_pow c L

/-- **`P/poly` with the literal bound from length `2` on.**  A language is in `P/poly` iff
some fan-in-two family decides it with `|C_n| ≤ n ^ c` for every `n ≥ 2`, the circuits at
lengths `0` and `1` being arbitrary.  [AB09, Def 6.5] (the book's `n ^ c`, up to the finitely
many lengths where it is degenerate; see `Language.not_inSIZE_pow`)

**Proof sketch.** (→) For `n ≥ 2`, `a ≤ n ^ a` and `n + 1 ≤ n ^ 2`, so
`a (n + 1) ^ k ≤ n ^ (a + 2k)`.  (←) Take `a = |C_0| + |C_1| + 1` and `k = c`: at `n ≤ 1`
the bound is at least `a`, and for `n ≥ 2`, `n ^ c ≤ (n + 1) ^ c ≤ a (n + 1) ^ c`. -/
theorem Language.inPPoly_iff_eventually (L : Language Bool) :
    L.InPPoly ↔ ∃ c, ∃ C : BoolCircuit.DAGCircuitFamily, C.HasFaninTwo ∧
      (∀ n, 2 ≤ n → (C.circuit n).size ≤ n ^ c) ∧ C.language = L := by
  constructor
  · rintro ⟨a, k, C, hG, hS, hL⟩
    refine ⟨a + 2 * k, C, hG, fun n hn => (hS n).trans ?_, hL⟩
    have h1 : a ≤ n ^ a := (Nat.lt_pow_self (by omega)).le
    have h2 : n + 1 ≤ n ^ 2 := by
      have : 2 * n ≤ n * n := Nat.mul_le_mul_right n hn
      rw [pow_two]; omega
    show a * (n + 1) ^ k ≤ _
    calc a * (n + 1) ^ k ≤ n ^ a * (n ^ 2) ^ k :=
          Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 k)
      _ = n ^ (a + 2 * k) := by rw [← pow_mul, ← pow_add]
  · rintro ⟨c, C, hG, hS, hL⟩
    refine ⟨(C.circuit 0).size + (C.circuit 1).size + 1, c, C, hG, fun n => ?_, hL⟩
    have hpos : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (by omega)
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
    · exact (by omega : (C.circuit 0).size ≤ _).trans (Nat.le_mul_of_pos_right _ hpos)
    · exact (by omega : (C.circuit 1).size ≤ _).trans (Nat.le_mul_of_pos_right _ hpos)
    · calc (C.circuit n).size ≤ n ^ c := hS n hn
        _ ≤ (n + 1) ^ c := Nat.pow_le_pow_left (by omega) c
        _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)

namespace BoolCircuit

/-- `P/poly` as a set of languages.  [AB09, Def 6.5] -/
def PPoly : Set (Language Bool) :=
  {L | L.InPPoly}

/-- Set membership in `PPoly` agrees with the predicate `Language.InPPoly`. -/
@[simp]
theorem mem_PPoly_iff (L : Language Bool) : L ∈ PPoly ↔ L.InPPoly :=
  Iff.rfl

end BoolCircuit
