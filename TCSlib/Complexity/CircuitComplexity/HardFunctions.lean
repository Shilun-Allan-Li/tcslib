/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Card
import TCSlib.Complexity.CircuitComplexity.Encoding

/-!
# Existence of hard Boolean functions

Arora–Barak's counting argument: there are more Boolean functions on `n` bits than
there are small circuits, so some function is computed by none of them.

## Main results

* `ACP.length_encodeCircuit_succ_le` — a circuit of size `S` on `n` variables has an
  encoding of fewer than `(n + 4) * S` bits.
* `ACP.encodeCircuit_injective` — distinct circuits have distinct encodings.
* `ACP.card_computable_le` — at most `2 ^ ((n + 4) * S)` functions
  `(Fin n → Bool) → Bool` are computed by a circuit of size at most `S`.
* `ACP.exists_not_eval_of_lt` — whenever `(n + 4) * S < 2 ^ n`, some function
  differs from every size-`≤ S` circuit at some input.  [AB09, Thm 6.21]
* `ACP.exists_hard_function` — the same with the explicit size bound
  `2 ^ n / (n + 5)`.  [AB09, Thm 6.21]

## Divergences from [AB09, Thm 6.21]

**AB's size bound `2 ^ n / (10 n)` is not proved here, and the two are not
comparable.** [AB09, Def 6.1]'s circuit is a DAG whose `∨`/`∧` gates have fan-in `2`
and whose `¬` gates have fan-in `1`, with size its number of vertices — one source
vertex per input variable, however often that variable is read.
`BoolCircuit.Circuit` is a *tree* with unbounded fan-in and negation folded into its
literals, and `Circuit.size` counts every node, so each literal *occurrence* costs a
node and no gate may be reused. "Computed by no circuit of size `≤ S`" therefore rules
out a far smaller family of objects than AB's does, and is a correspondingly weaker
conclusion at any `S`.

The bound proved is `(n + 4) * S < 2 ^ n`, i.e. hardness at size `2 ^ n / (n + 5)`.
It comes from `Encoding.lean`'s serialiser: a leaf costs `idx + 3` bits, its index
being written in unary, and a gate costs three bits plus one per child, so size `S`
fits in fewer than `(n + 4) * S` bits, against the `9 · S · log S` AB cites for an
adjacency list. Since `n + 5 < 10 n` for `n ≥ 1`, `2 ^ n / (n + 5)` is the larger of
the two numbers — a unary index costs `n` bits a leaf, the same order as AB's
`log S ≈ n`, against AB's generous constant `9`. That is not a strengthening of AB: it
is a weaker statement that happens to admit a larger constant.

`n > 1` is not assumed. `(n + 4) * S < 2 ^ n` forces `S = 0` for `n ≤ 2`, and
`Circuit.size` is never `0`, so the conclusion is vacuous there; it first has content
at `n = 3`.

`ACP.size_le_length_encodeSigma`, the hook `ch6/PLAN.md` names, bounds a circuit's
size by its encoding's length. The count needs the converse;
`length_encodeCircuit_succ_le` below supplies it, and belongs in `Encoding.lean`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ACP

open BoolCircuit

/-! ## Bit strings as numbers -/

/-- A bit string as a number: its bits, terminated by a `1` so that the length is
recoverable. -/
private def bitsToNat (w : List Bool) : ℕ :=
  Nat.ofDigits 2 ((w.map fun b => if b then 1 else 0) ++ [1])

/-- Every digit of `bitsToNat`'s digit list is `0` or `1`. -/
private theorem bitsToNat_digits_lt (w : List Bool) :
    ∀ d ∈ (w.map fun b => if b then 1 else 0) ++ [1], d < 2 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨b, -, rfl⟩ := List.mem_map.mp hd
    cases b <;> norm_num
  · simp only [List.mem_singleton] at hd
    omega

/-- A string of `k` bits codes a number below `2 ^ (k + 1)`. -/
private theorem bitsToNat_lt (w : List Bool) : bitsToNat w < 2 ^ (w.length + 1) := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 2) (by norm_num) (bitsToNat_digits_lt w)
  simpa [bitsToNat] using h

/-- Distinct bit strings code distinct numbers. -/
private theorem bitsToNat_injective : Function.Injective bitsToNat := by
  have key : ∀ w : List Bool,
      Nat.digits 2 (bitsToNat w) = (w.map fun b => if b then 1 else 0) ++ [1] := by
    intro w
    refine Nat.digits_ofDigits 2 (by norm_num) _ (bitsToNat_digits_lt w) ?_
    intro hne
    rw [List.getLast_append_singleton]
    omega
  intro w₁ w₂ h
  have h₂ : (w₁.map fun b => if b then 1 else 0) ++ [1]
      = (w₂.map fun b => if b then 1 else 0) ++ [1] := by
    rw [← key w₁, ← key w₂, h]
  have hf : Function.Injective (fun b : Bool => if b then 1 else 0) := by decide
  exact List.map_injective_iff.mpr hf (List.append_cancel_right h₂)

/-! ## How long a circuit's encoding is -/

/-- A literal's encoding is `idx + 3` bits: a tag bit, a sign bit, and the index
in unary. -/
private theorem length_encodeCircuit_lit {n : ℕ} :
    ∀ (k : ℕ) (h : k < n) (s : Bool),
      (encodeCircuit (Circuit.lit (n := n) ⟨⟨k, h⟩, s⟩)).length = k + 3
  | 0, _, _ => by simp only [encodeCircuit]; rfl
  | k + 1, h, s => by
      have h' : k < n := Nat.lt_of_succ_lt h
      have step : (encodeCircuit (Circuit.lit (n := n) ⟨⟨k + 1, h⟩, s⟩)).length
          = (encodeCircuit (Circuit.lit (n := n) ⟨⟨k, h'⟩, s⟩)).length + 1 := by
        simp only [encodeCircuit]; rfl
      rw [step, length_encodeCircuit_lit k h' s]

/-- A circuit of size `S` on `n` variables encodes into fewer than `(n + 4) * S` bits.

**Proof sketch.** Structural induction. A leaf's encoding is a tag bit, a sign bit and
its variable index in unary, so `idx + 3 < n + 4` bits against a size of one. A gate's
encoding is a tag bit, a connective bit and its children block, the block being one
continue bit per child, the children's own encodings, and a stop bit; a side induction
on the list of children shows the block is at most `(n + 4)` times the children's total
size, plus one — each child pays for its own continue bit out of the one bit of slack
the statement carries. The gate's two tag bits, its stop bit and that slack come to
four bits, which is at most the `n + 4` the gate's own node contributes. -/
theorem length_encodeCircuit_succ_le {n : ℕ} (C : Circuit n) :
    (encodeCircuit C).length + 1 ≤ (n + 4) * C.size := by
  induction C using Circuit.ind with
  | hlit l =>
      obtain ⟨⟨k, hk⟩, s⟩ := l
      rw [length_encodeCircuit_lit k hk s]
      simp only [Circuit.size, Nat.mul_one]
      omega
  | hnode b cs ih =>
      have hlist : ∀ ds : List (Circuit n),
          (∀ d ∈ ds, (encodeCircuit d).length + 1 ≤ (n + 4) * d.size) →
          (encodeChildren ds).length ≤
            (n + 4) * ds.foldr (fun d acc => d.size + acc) 0 + 1 := by
        intro ds hds
        induction ds with
        | nil => simp [encodeChildren_nil]
        | cons d ds ihd =>
            have h1 := hds d List.mem_cons_self
            have h2 := ihd fun e he => hds e (List.mem_cons_of_mem _ he)
            rw [encodeChildren_cons]
            simp only [List.length_cons, List.length_append, List.foldr_cons, Nat.mul_add]
            omega
      have hsum := hlist cs ih
      rw [encodeCircuit_node]
      simp only [List.length_cons, Circuit.size, Nat.mul_add, Nat.mul_one]
      omega

/-- Distinct circuits have distinct encodings. -/
theorem encodeCircuit_injective {n : ℕ} : Function.Injective (encodeCircuit (n := n)) := by
  intro C D h
  have hC := readCircuit_encodeCircuit C (encodeCircuit C).length [] le_rfl
  have hD := readCircuit_encodeCircuit D (encodeCircuit D).length [] le_rfl
  rw [List.append_nil] at hC hD
  rw [h] at hC
  simpa using hC.symm.trans hD

/-! ## The counting argument -/

/-- At most `2 ^ ((n + 4) * S)` Boolean functions on `n` variables are computed by a
circuit of size at most `S`.  [AB09, Thm 6.21]

**Proof sketch.** Pick, for each function in the set, a circuit of size at most `S`
computing it, and send the function to the number coding that circuit's encoding. The
map is injective on the set: the code determines the bit string, the bit string
determines the circuit, and the circuit determines the function it computes. Its values
lie below `2 ^ ((n + 4) * S)`, because a circuit of size at most `S` encodes into fewer
than `(n + 4) * S` bits. -/
theorem card_computable_le (n S : ℕ) :
    {f : (Fin n → Bool) → Bool | ∃ C : Circuit n, C.size ≤ S ∧ C.eval = f}.ncard
      ≤ 2 ^ ((n + 4) * S) := by
  classical
  haveI : Nonempty (Circuit n) := ⟨Circuit.node true []⟩
  have key : ∀ f ∈ {f : (Fin n → Bool) → Bool | ∃ C : Circuit n, C.size ≤ S ∧ C.eval = f},
      ∃ C : Circuit n, C.size ≤ S ∧ C.eval = f := fun _ hf => hf
  choose! g hg₁ hg₂ using key
  have hmain := Set.ncard_le_ncard_of_injOn
    (t := (↑(Finset.range (2 ^ ((n + 4) * S))) : Set ℕ))
    (fun f => bitsToNat (encodeCircuit (g f)))
    (fun f hf => by
      simp only [Finset.coe_range, Set.mem_Iio]
      calc bitsToNat (encodeCircuit (g f)) < 2 ^ ((encodeCircuit (g f)).length + 1) :=
            bitsToNat_lt _
        _ ≤ 2 ^ ((n + 4) * S) :=
            Nat.pow_le_pow_right (by norm_num)
              (le_trans (length_encodeCircuit_succ_le (g f))
                (Nat.mul_le_mul_left _ (hg₁ f hf))))
    (fun f₁ h₁ f₂ h₂ heq => by
      have hg : g f₁ = g f₂ := encodeCircuit_injective (bitsToNat_injective heq)
      rw [← hg₂ f₁ h₁, ← hg₂ f₂ h₂, hg])
    (Finset.finite_toSet _)
  rwa [Set.ncard_coe_finset, Finset.card_range] at hmain

/-- Some Boolean function on `n` variables differs, at some input, from every circuit of
size at most `S`, whenever `(n + 4) * S < 2 ^ n`.  [AB09, Thm 6.21]

**Proof sketch.** There are `2 ^ 2 ^ n` functions on `n` variables and, by
`card_computable_le`, at most `2 ^ ((n + 4) * S)` of them are computed by a circuit of
size at most `S`; the hypothesis makes the second number the smaller, so the computable
ones are not all of them. A function outside that set is computed by no such circuit,
and two Boolean functions that are not equal differ at a point. -/
theorem exists_not_eval_of_lt {n S : ℕ} (h : (n + 4) * S < 2 ^ n) :
    ∃ f : (Fin n → Bool) → Bool, ∀ C : Circuit n, C.size ≤ S → ∃ x, C.eval x ≠ f x := by
  classical
  set T : Set ((Fin n → Bool) → Bool) :=
    {f | ∃ C : Circuit n, C.size ≤ S ∧ C.eval = f}
  have hcard : T.ncard ≤ 2 ^ ((n + 4) * S) := card_computable_le n S
  have hcardF : Nat.card ((Fin n → Bool) → Bool) = 2 ^ 2 ^ n := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun]
    simp
  obtain ⟨f, hf⟩ : ∃ f : (Fin n → Bool) → Bool, f ∉ T := by
    by_contra hcon
    push_neg at hcon
    rw [Set.eq_univ_of_forall hcon, Set.ncard_univ, hcardF] at hcard
    exact absurd (lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) h) hcard) (lt_irrefl _)
  refine ⟨f, fun C hC => ?_⟩
  by_contra hcon
  push_neg at hcon
  exact hf ⟨C, hC, funext hcon⟩

/-- For every `n` there is a Boolean function on `n` variables that no circuit of size
at most `2 ^ n / (n + 5)` computes.  [AB09, Thm 6.21]

**Proof sketch.** Immediate from `exists_not_eval_of_lt`: if `2 ^ n / (n + 5)` is zero
the hypothesis is `0 < 2 ^ n`, and otherwise multiplying it by `n + 4` rather than
`n + 5` strictly decreases the product, which `n + 5` times the quotient already keeps
below `2 ^ n`. -/
theorem exists_hard_function (n : ℕ) :
    ∃ f : (Fin n → Bool) → Bool,
      ∀ C : Circuit n, C.size ≤ 2 ^ n / (n + 5) → ∃ x, C.eval x ≠ f x := by
  refine exists_not_eval_of_lt ?_
  rcases Nat.eq_zero_or_pos (2 ^ n / (n + 5)) with hq | hq
  · rw [hq, Nat.mul_zero]
    exact Nat.pow_pos (by norm_num)
  · calc (n + 4) * (2 ^ n / (n + 5)) < (n + 5) * (2 ^ n / (n + 5)) :=
          (Nat.mul_lt_mul_right hq).mpr (by omega)
      _ = 2 ^ n / (n + 5) * (n + 5) := Nat.mul_comm _ _
      _ ≤ 2 ^ n := Nat.div_mul_le_self _ _

/-! Degenerate arities. `Circuit.size` is never `0` and `2 ^ n / (n + 5)` is `0` for
`n ≤ 2`, so `exists_hard_function` says nothing below `n = 3`; at `n = 3` it excludes
every single-literal circuit. -/

example (C : Circuit 2) : ¬ C.size ≤ 2 ^ 2 / (2 + 5) := by
  cases C <;> simp [Circuit.size]

example : ∃ f : (Fin 3 → Bool) → Bool,
    ∀ C : Circuit 3, C.size ≤ 1 → ∃ x, C.eval x ≠ f x := by
  have h := exists_hard_function 3
  norm_num at h
  exact h

end ACP
