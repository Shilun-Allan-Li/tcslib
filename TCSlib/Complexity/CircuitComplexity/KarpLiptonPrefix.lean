/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.PolyHierarchy.Padding
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.CircuitComplexity.CircuitEvalRun
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionValid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Karp–Lipton: the prefix language

The proof of the Karp–Lipton theorem [AB09, Thm 6.19] applies the hypothesis
`NP ⊆ P/poly` not to the `Π₂ᵖ` verifier itself but to its *search* version: the
language of pairs `⟨y, p⟩` such that the partial witness `p` extends to a full witness
`v` with `⟨y, v⟩ ∈ V` (the decision problem behind the search-to-decision reduction of
[AB09, Thm 2.18], which the book applies to the true formulas `∀ u ∃ v ϕ(u, v)`). This file defines that language
and proves it is in `NP`, together with the polynomial-time glue used by the Karp–Lipton
verifier (`KarpLipton.lean`); the generic closure glue for `P` it uses is in
`TCSlib.Complexity.ClassNP.PClosure`.

The partial witness `p` is written in the **fixed-length marker encoding**
`1ᵏ 0 p` with `k + |p| = m`: every query about one `y` then has the same length, so a
*single* circuit of the `P/poly` family answers all of them. The marker is removed by a
one-pass transducer (`Complexity.KarpLipton.dropMarker`).

## Main definitions

* `Complexity.KarpLipton.dropMarker` — strip a leading `1ᵏ 0` (a one-pass transducer).
* `Complexity.KarpLipton.wLen` — the witness length `C (|fst y| + 1)^c` attached to `y`.
* `Complexity.KarpLipton.prefixLangOf` — the prefix (partial-witness) language of a
  verifier `V` with witness-length function `ℓ`; `Complexity.KarpLipton.prefixLang` — the
  instance used by Karp–Lipton.

## Main results

* `Complexity.KarpLipton.polyTimeComputable_dropMarker`, `dropMarker_marker`.
* `Complexity.KarpLipton.mem_prefixLangOf_iff`, `mem_prefixLang_iff` — the prefix
  language on a marker-encoded partial witness.
* `Complexity.KarpLipton.prefixLangOf_mem_NP`, `prefixLang_mem_NP` — the prefix language
  is in `NP`.

## Divergences from [AB09]

* [AB09] runs the search-to-decision reduction on formulas `ϕ(u, ·)` (a partial
  assignment hard-wired), relying on the `Π₂ᵖ`-completeness of the quantified formulas
  `∀ u ∃ v ϕ(u, v)`. We avoid
  completeness (which needs the Cook–Levin machinery) and run it directly on the
  verifier `V` of an arbitrary `Π₂ᵖ` language: the "partial assignment" is a prefix of
  the certificate.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.5, Theorem 2.18; §6.4, Theorem 6.19, p. 114.)
-/

namespace Complexity.KarpLipton

open Turing Complexity.PolyHierarchy BoolCircuit.CktSatReduction

/-! ### Stripping a leading marker -/

/-- Transition of the marker-stripping transducer: state `false` skips the leading `1`s,
the first `0` moves to state `true`, which copies the rest. -/
def dropTr : Bool → Bool → Bool
  | false, b => !b
  | true, _ => true

/-- Emission of the marker-stripping transducer: nothing in state `false`, a copy of the
bit in state `true`. -/
def dropOut : Bool → Bool → Option Bool
  | false, _ => none
  | true, b => some b

/-- **Strip a leading marker** `1ᵏ 0`: `dropMarker (1ᵏ 0 p) = p`. On a word with no `0`
the result is empty. -/
def dropMarker (w : List Bool) : List Bool := transduce dropTr dropOut false w

/-- In the copying state the transducer is the identity. -/
theorem transduce_drop_true (p : List Bool) : transduce dropTr dropOut true p = p := by
  induction p with
  | nil => rfl
  | cons b p ih => simp [transduce, dropTr, dropOut, ih]

/-- Stripping the marker `1ᵏ 0` returns the rest of the word. -/
@[simp] theorem dropMarker_marker (k : ℕ) (p : List Bool) :
    dropMarker (List.replicate k true ++ false :: p) = p := by
  unfold dropMarker
  induction k with
  | zero => simp [transduce, dropTr, dropOut, transduce_drop_true]
  | succ k ih => simpa [List.replicate_succ, transduce, dropTr, dropOut] using ih

/-- Marker stripping is polynomial-time (a one-pass transducer). -/
theorem polyTimeComputable_dropMarker : PolyTimeComputable dropMarker :=
  polyTimeComputable_transduce dropTr dropOut false

/-! ### The prefix language -/

/-- The witness length attached to a word `y = ⟨x, u⟩`: `C (|x| + 1)^c`, read off the
first component of `y`. -/
def wLen (C c : ℕ) (y : List Bool) : ℕ := C * ((pairFstD y).length + 1) ^ c

/-- On `y = ⟨x, u⟩` the witness length is `C (|x| + 1)^c`. -/
@[simp] theorem wLen_pairEncode (C c : ℕ) (x u : List Bool) :
    wLen C c (pairEncode x u) = C * (x.length + 1) ^ c := by
  simp [wLen]

/-- **The prefix language** of a verifier `V` with witness-length function `ℓ` (the
decision version used in the search-to-decision reduction of [AB09, Thm 2.18]):
`⟨y, e⟩` is in it iff, writing `p` for `e` with its leading marker `1ᵏ 0` stripped,
`p` extends to a word `p s` of length `ℓ y` with `⟨y, p s⟩ ∈ V`. -/
def prefixLangOf (ℓ : List Bool → ℕ) (V : Language Bool) : Language Bool :=
  {q | ∃ s : List Bool, (dropMarker (pairSndD q) ++ s).length = ℓ (pairFstD q) ∧
    pairEncode (pairFstD q) (dropMarker (pairSndD q) ++ s) ∈ V}

/-- Membership in the prefix language, unfolded. -/
theorem mem_prefixLangOf {ℓ : List Bool → ℕ} {V : Language Bool} {q : List Bool} :
    q ∈ prefixLangOf ℓ V ↔ ∃ s : List Bool,
      (dropMarker (pairSndD q) ++ s).length = ℓ (pairFstD q) ∧
        pairEncode (pairFstD q) (dropMarker (pairSndD q) ++ s) ∈ V := Iff.rfl

/-- **The prefix language on a marker-encoded partial witness**: `⟨y, 1ᵏ 0 p⟩` is in it
iff `p` extends to a witness `p s` of length `ℓ y` accepted by `V`. -/
theorem mem_prefixLangOf_iff (ℓ : List Bool → ℕ) (V : Language Bool) (y p : List Bool)
    (k : ℕ) :
    pairEncode y (List.replicate k true ++ false :: p) ∈ prefixLangOf ℓ V ↔
      ∃ s : List Bool, (p ++ s).length = ℓ y ∧ pairEncode y (p ++ s) ∈ V := by
  rw [mem_prefixLangOf]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, dropMarker_marker]

/-- **The prefix language is in `NP`** when the verifier is in `P` and the witness length
`ℓ` is a polynomially bounded unary polynomial-time length function.

**Proof sketch.** Use the bounded-certificate form of `NP`
(`Complexity.mem_NP_iff_exists_length_le`) with the certificate `s`: the verifier strips
the marker (a transducer), checks `|p s| = ℓ(fst q)` by a length comparison with the
unary template `1^{ℓ(fst q)}`, and runs `V` on `⟨fst q, p s⟩`; all pieces are
polynomial-time, so the verifier is an intersection of two languages in `P`. The
certificate length is at most `ℓ(fst q) ≤ A (|fst q|+1)^a ≤ A (|q|+1)^a`, since a
projection is never longer than the word. -/
theorem prefixLangOf_mem_NP {ℓ : List Bool → ℕ} {V : Language Bool} (hV : V ∈ P)
    (hℓ : UnaryPT ℓ) {A a : ℕ} (hb : ∀ y, ℓ y ≤ A * (y.length + 1) ^ a) :
    prefixLangOf ℓ V ∈ NP := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  -- the pieces of the verifier input `⟨q, s⟩`
  have hy : PolyTimeComputable (fun z => pairFstD (pairFstD z)) := hF.comp hF
  have hps : PolyTimeComputable
      (fun z => dropMarker (pairSndD (pairFstD z)) ++ pairSndD z) :=
    PolyTimeComputable.append (polyTimeComputable_dropMarker.comp (hS.comp hF)) hS
  have hM : PolyTimeComputable
      (fun z => List.replicate (ℓ (pairFstD (pairFstD z))) true) := hℓ.comp hy
  set W : Language Bool :=
    {z | z ∈ {z : List Bool | (List.replicate (ℓ (pairFstD (pairFstD z))) true).length =
        (dropMarker (pairSndD (pairFstD z)) ++ pairSndD z).length} ∧
      z ∈ (fun z => pairEncode (pairFstD (pairFstD z))
        (dropMarker (pairSndD (pairFstD z)) ++ pairSndD z)) ⁻¹' V} with hW
  have hWP : W ∈ P :=
    inter_mem_P (lenEq_preimage_mem_P hM hps) (preimage_mem_P hV (hy.pairEncode hps))
  refine mem_NP_iff_exists_length_le.mpr ⟨A, a, W, hWP, fun q => ?_⟩
  have hWm : ∀ z, z ∈ W ↔
      (List.replicate (ℓ (pairFstD (pairFstD z))) true).length =
        (dropMarker (pairSndD (pairFstD z)) ++ pairSndD z).length ∧
      pairEncode (pairFstD (pairFstD z)) (dropMarker (pairSndD (pairFstD z)) ++ pairSndD z) ∈ V :=
    fun z => Iff.rfl
  simp only [mem_prefixLangOf, hWm, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
  constructor
  · rintro ⟨s, hs, hv⟩
    refine ⟨s, ?_, hs.symm, hv⟩
    have h1 := length_pairFstD_le q
    have h2 : s.length ≤ ℓ (pairFstD q) := by
      rw [← hs]; simp
    refine (h2.trans (hb _)).trans ?_
    exact Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) a)
  · rintro ⟨s, -, hs, hv⟩
    exact ⟨s, hs.symm, hv⟩

/-- **The prefix language used by Karp–Lipton**: witness length `C (|x|+1)^c` read off the
first component of `y = ⟨x, u⟩` (`Complexity.KarpLipton.wLen`). -/
def prefixLang (C c : ℕ) (V : Language Bool) : Language Bool := prefixLangOf (wLen C c) V

/-- Membership in the Karp–Lipton prefix language, unfolded. -/
theorem mem_prefixLang {C c : ℕ} {V : Language Bool} {q : List Bool} :
    q ∈ prefixLang C c V ↔ ∃ s : List Bool,
      (dropMarker (pairSndD q) ++ s).length = wLen C c (pairFstD q) ∧
        pairEncode (pairFstD q) (dropMarker (pairSndD q) ++ s) ∈ V := Iff.rfl

/-- **The prefix language on a marker-encoded partial witness**: `⟨y, 1ᵏ 0 p⟩` is in it
iff `p` extends to a witness `p s` of the right length accepted by `V`. -/
theorem mem_prefixLang_iff (C c : ℕ) (V : Language Bool) (y p : List Bool) (k : ℕ) :
    pairEncode y (List.replicate k true ++ false :: p) ∈ prefixLang C c V ↔
      ∃ s : List Bool, (p ++ s).length = wLen C c y ∧ pairEncode y (p ++ s) ∈ V :=
  mem_prefixLangOf_iff _ V y p k

/-- **The Karp–Lipton prefix language is in `NP`** when the verifier is in `P`
(`prefixLangOf_mem_NP` with `ℓ = wLen C c ≤ C (|y|+1)^c`). -/
theorem prefixLang_mem_NP {C c : ℕ} {V : Language Bool} (hV : V ∈ P) :
    prefixLang C c V ∈ NP :=
  prefixLangOf_mem_NP hV (unaryPT_poly C c polyTimeComputable_pairFstD) (A := C) (a := c)
    fun y => Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by
      have := length_pairFstD_le y; omega) c)

end Complexity.KarpLipton
