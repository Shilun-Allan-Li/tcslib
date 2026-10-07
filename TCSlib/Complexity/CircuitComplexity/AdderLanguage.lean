/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.Adder
import TCSlib.Complexity.CircuitComplexity.PPoly

/-!
# Arora–Barak Example 6.3, part 2: the addition language is in `SIZE(O(n))`

[AB09, Ex 6.3]: "The language `{⟨m, n, m + n⟩ : m, n ∈ ℤ}` also has linear-sized circuits
that implement the grade-school algorithm for addition."  We fix an encoding of the triples
as Boolean strings, and decide the resulting language with the ripple-carry circuits of
`Adder.lean` in the book's model (`Language.InSIZE` over `BoolCircuit.DAGCircuit`).  The
first half of the example (the all-ones language) is in `SizeClasses.lean`.

## Main definitions

* `Language.addition` — the words `a ++ b ++ c` with three blocks of a common width and
  `bitsVal c = bitsVal a + bitsVal b`.
* `BoolCircuit.natToBits k m` — the `k`-bit little-endian encoding of `m`.
* `BoolCircuit.adderFamily` — `adderCircuit n` at lengths divisible by `3`, else the
  constant-`false` circuit `constCircuit n false` (`DAGCircuit.lean`).

## Main results

* `BoolCircuit.adderFamily_language` — the family decides `Language.addition`.
* `Language.addition_inSIZE` — `Language.addition ∈ SIZE(6 n + 4)`.  [AB09, Ex 6.3]
* `Language.addition_inPPoly` — hence `Language.addition ∈ P/poly`.
* `Language.natToBits_mem_addition`, `Language.exists_natToBits_mem_addition` — sanity
  check: every triple `⟨m, n, m + n⟩` is encoded in the language.

## Divergences from [AB09, Ex 6.3]

* **Encoding.**  [AB09] leaves the encoding of `⟨m, n, m + n⟩` unspecified.  A word of
  length `3 k` is read as three `k`-bit little-endian blocks `a`, `b`, `c`, concatenated
  and zero-padded to the common width `k`; it is in the language iff
  `val c = val a + val b`.  So a triple `⟨m, n, m + n⟩` is encoded at every width `k` with
  `m + n < 2 ^ k` (leading zeros allowed), and the circuit checks that the final carry is
  `0`.  Words whose length is not a multiple of `3` encode no triple and are rejected.
* **`ℕ` rather than `ℤ`.**  [AB09] writes `m, n ∈ ℤ`; we take natural numbers, the setting
  of the grade-school algorithm the example describes (signs would need a further
  encoding convention the book does not give).
* **Explicit constant.**  "Linear-sized" is `SIZE(6 n + 4)`: the ripple-carry circuit on
  `n = 3 k` inputs has `18 k + 4 = 6 n + 4` vertices, inputs included as in [AB09, Def 6.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Example 6.3.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

/-! ## Encoding numbers -/

/-- The `k`-bit little-endian encoding of `m`: bit `j` is `m.testBit j`, for `j < k`
(so `m` is truncated mod `2 ^ k`). -/
def natToBits (k m : ℕ) : List Bool :=
  List.ofFn fun j : Fin k => m.testBit j

/-- The `k`-bit encoding has `k` bits. -/
@[simp] theorem length_natToBits (k m : ℕ) : (natToBits k m).length = k := by
  simp [natToBits]

/-- Decoding the `k`-bit encoding of `m < 2 ^ k` returns `m`. -/
theorem bitsVal_natToBits {k m : ℕ} (h : m < 2 ^ k) : bitsVal (natToBits k m) = m := by
  induction k generalizing m with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    have hcons : natToBits (k + 1) m = m.testBit 0 :: natToBits k (m / 2) := by
      simp only [natToBits, List.ofFn_succ, Fin.val_zero, Fin.val_succ, Nat.testBit_succ]
    rw [hcons]
    simp only [bitsVal, List.map_cons, Nat.ofDigits_cons] at ih ⊢
    rw [ih (by rw [pow_succ] at h; omega), Nat.toNat_testBit, pow_zero, Nat.div_one]
    omega

/-! ## The circuit family -/

/-- The family deciding the addition language: the ripple-carry circuit at lengths
divisible by `3`, the constant-`false` circuit elsewhere.  [AB09, Ex 6.3] -/
def adderFamily : DAGCircuitFamily where
  circuit n := if n % 3 = 0 then adderCircuit n else constCircuit n false

end BoolCircuit

open BoolCircuit in
/-- The addition language `{⟨m, n, m + n⟩}` of [AB09, Ex 6.3]: the words `a ++ b ++ c`
made of three blocks of a common width `k`, read as little-endian numbers, with
`val c = val a + val b`.  *Encoding (the book leaves it unspecified):* blocks are
concatenated and zero-padded to a common width, so a triple is encoded at every width
`k` large enough for `m + n`; words whose length is not a multiple of `3` are not in the
language.  The empty word (width `0`) is in the language: it encodes `⟨0, 0, 0⟩`.  Every
triple is encoded (`Language.natToBits_mem_addition`).  [AB09] writes `m, n ∈ ℤ`; we take
`m, n ∈ ℕ`. -/
def Language.addition : Language Bool :=
  {w | ∃ a b c : List Bool, a.length = c.length ∧ b.length = c.length ∧ w = a ++ b ++ c ∧
    bitsVal c = bitsVal a + bitsVal b}

namespace BoolCircuit

/-- The family `adderFamily` has fan-in two. -/
theorem adderFamily_hasFaninTwo : adderFamily.HasFaninTwo := by
  intro n
  simp only [adderFamily]
  split
  · exact adderCircuit_isFaninTwo n
  · exact constCircuit_isFaninTwo n false

/-- The length-`n` circuit of `adderFamily` has at most `6 n + 4` vertices
(`n + 15 ⌊n / 3⌋ + 4 ≤ 6 n + 4` for the ripple-carry circuit, `n + 1` otherwise). -/
theorem adderFamily_size_le (n : ℕ) : (adderFamily.circuit n).size ≤ 6 * n + 4 := by
  simp only [adderFamily]
  split
  · rw [adderCircuit_size]; omega
  · rw [constCircuit_size]; omega

/-- `adderFamily` decides `Language.addition`.  [AB09, Ex 6.3]

**Proof sketch.** At a length not divisible by `3` the family outputs `false`, and no word
of the language has such a length (it is `3 |c|`).  At a length `3 k`, cut the word into
its blocks of width `k`; `adderCircuit_eval_append` says the circuit accepts iff the
blocks satisfy `val c = val a + val b`, and any decomposition witnessing membership has
blocks of width `k`, so it is this one. -/
theorem adderFamily_language : adderFamily.language = Language.addition := by
  ext w
  simp only [DAGCircuitFamily.mem_language_iff, adderFamily, Language.addition]
  split_ifs with h
  · constructor
    · intro hacc
      -- cut `w` into its three blocks of width `|w| / 3`
      obtain ⟨a, b, c, ha, hb, rfl⟩ : ∃ a b c : List Bool,
          a.length = c.length ∧ b.length = c.length ∧ w = a ++ b ++ c := by
        refine ⟨w.take (w.length / 3), (w.drop (w.length / 3)).take (w.length / 3),
          w.drop (2 * (w.length / 3)), by simp; omega, by simp; omega, ?_⟩
        rw [← List.take_add, show w.length / 3 + w.length / 3 = 2 * (w.length / 3) by omega,
          List.take_append_drop]
      exact ⟨a, b, c, ha, hb, rfl, (adderCircuit_eval_append ha hb).mp hacc⟩
    · rintro ⟨a, b, c, ha, hb, rfl, hv⟩
      exact (adderCircuit_eval_append ha hb).mpr hv
  · simp only [constCircuit_eval, Bool.false_eq_true, false_iff]
    rintro ⟨a, b, c, ha, hb, rfl, _⟩
    apply h
    simp
    omega

end BoolCircuit

/-- [AB09, Ex 6.3], part 2: the addition language has linear-size circuits,
`Language.addition ∈ SIZE(6 n + 4)`.  Deviation: the book says "linear-sized"; the constant
is made explicit, and the encoding is the one fixed in `Language.addition`. -/
theorem Language.addition_inSIZE : Language.addition.InSIZE (fun n => 6 * n + 4) :=
  ⟨BoolCircuit.adderFamily, BoolCircuit.adderFamily_hasFaninTwo,
    BoolCircuit.adderFamily_size_le, BoolCircuit.adderFamily_language⟩

/-- [AB09, Ex 6.3], part 2: consequently the addition language is in `P/poly`. -/
theorem Language.addition_inPPoly : Language.addition.InPPoly :=
  Language.addition_inSIZE.inPPoly (a := 6) (k := 1) fun n => by simp; omega

/-- Every triple `⟨m, n, m + n⟩` is encoded in `Language.addition` at every width `k` with
`m + n < 2 ^ k`: the word `bits_k m ++ bits_k n ++ bits_k (m + n)` is in the language. -/
theorem Language.natToBits_mem_addition {m n k : ℕ} (h : m + n < 2 ^ k) :
    BoolCircuit.natToBits k m ++ BoolCircuit.natToBits k n ++ BoolCircuit.natToBits k (m + n) ∈
      Language.addition := by
  refine ⟨_, _, _, by simp, by simp, rfl, ?_⟩
  rw [BoolCircuit.bitsVal_natToBits h, BoolCircuit.bitsVal_natToBits (by omega),
    BoolCircuit.bitsVal_natToBits (by omega)]

/-- Every triple `⟨m, n, m + n⟩` of natural numbers has an encoding in `Language.addition`
(e.g. at width `m + n + 1`). -/
theorem Language.exists_natToBits_mem_addition (m n : ℕ) :
    ∃ k, BoolCircuit.natToBits k m ++ BoolCircuit.natToBits k n ++
      BoolCircuit.natToBits k (m + n) ∈ Language.addition :=
  ⟨m + n + 1, Language.natToBits_mem_addition (Nat.lt_two_pow_self.trans
    (Nat.pow_lt_pow_right (by norm_num) (by omega)))⟩
