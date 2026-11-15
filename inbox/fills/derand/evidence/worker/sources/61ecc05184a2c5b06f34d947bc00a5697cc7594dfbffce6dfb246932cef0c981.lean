/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.PClosure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time toolkit for the polynomial hierarchy

The machine-level facts that the quantifier manipulations of [AB09, Theorem 5.4] need,
assembled only from the proved machine catalog
(`TCSlib.Complexity.TuringMachine.Build.Primitives`) and the closure calculus of
`Complexity.PolyTimeComputable` (the generic pair projections, branching, length tests
and `P`-closure facts are in `TCSlib.Complexity.ClassNP.PolyTimePairing` and
`TCSlib.Complexity.ClassNP.PClosure`):

* **certificate padding** `padDecode`: a polynomial-time map sending *every* word of a
  longer length `B` to a word of the target length `|s|`, and onto it. Because it is
  total and surjective it transfers `∃` and `∀` blocks alike — the padding step of
  [AB09, proof of Theorem 5.4] ("certificates of length `q(|x|)` can be padded");
* the block-wise decoder `tupleDecode` on nested-pair tuples, polynomial-time for every
  fixed depth;
* `UnaryPT ℓ`: the length function `ℓ` is computable in unary in polynomial time.

## Main definitions

* `Complexity.PolyHierarchy.padDecode` — total, surjective certificate un-padding.
* `Complexity.PolyHierarchy.tupleDecode` — block-wise decoding of a nested tuple.
* `Complexity.PolyHierarchy.UnaryPT` — unary polynomial-time length functions.

## Main results

* `Complexity.PolyHierarchy.polyTimeComputable_padDecode` — un-padding is polynomial-time.
* `Complexity.PolyHierarchy.exists_padDecode_eq` — every target word is hit from every
  longer length.
* `Complexity.PolyHierarchy.polyTimeComputable_tupleDecode` — block-wise decoding is
  polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§5.2, Definition 5.3 and Theorem 5.4.)
-/

namespace Complexity.PolyHierarchy

open Turing

/-! ### Certificate padding -/

/-- **Un-padding a certificate.** Given a template `s` (only its length matters) and a
padded word `v`, strip `v` at its last `true` (`Turing.splitAtLastTrue`); if the prefix
has length `|s|` return it, and otherwise return `s` itself. The result always has
length `|s|`, and every word of length `|s|` is the image of a word of any longer length
(`Complexity.PolyHierarchy.exists_padDecode_eq`), so replacing a block of length `|s|` by
a padded block transfers both `∃` and `∀` quantifiers. -/
def padDecode (s v : List Bool) : List Bool :=
  match splitAtLastTrue v with
  | some u => if u.length = s.length then u else s
  | none => s

/-- Un-padding always produces a word of the template's length. -/
@[simp] theorem length_padDecode (s v : List Bool) : (padDecode s v).length = s.length := by
  unfold padDecode
  split
  · split <;> simp_all
  · rfl

/-- Dropping a block of `false`s from the front of a reversed marker word. -/
private theorem dropWhile_replicate_false (k : ℕ) (r : List Bool) :
    (List.replicate k false ++ true :: r).dropWhile (fun b => !b) = true :: r := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih]

/-- Stripping a marker suffix `1 0ᵏ` recovers the word before the marker. -/
theorem splitAtLastTrue_marker (u : List Bool) (k : ℕ) :
    splitAtLastTrue (u ++ true :: List.replicate k false) = some u := by
  unfold splitAtLastTrue
  have h : (u ++ true :: List.replicate k false).reverse =
      List.replicate k false ++ true :: u.reverse := by
    simp [List.reverse_append, List.reverse_replicate]
  rw [h, dropWhile_replicate_false]
  simp

/-- Un-padding inverts marker padding: `padDecode s (u ++ 1 0ᵏ) = u` when `|u| = |s|`. -/
theorem padDecode_marker {s u : List Bool} (h : u.length = s.length) (k : ℕ) :
    padDecode s (u ++ true :: List.replicate k false) = u := by
  simp [padDecode, splitAtLastTrue_marker, h]

/-- **Every target word is reachable from every longer length**: if `|u| = |s| < B`,
some word `v` of length exactly `B` un-pads to `u`. -/
theorem exists_padDecode_eq {s u : List Bool} {B : ℕ} (h : u.length = s.length)
    (hB : s.length < B) : ∃ v : List Bool, v.length = B ∧ padDecode s v = u := by
  refine ⟨u ++ true :: List.replicate (B - s.length - 1) false, ?_, padDecode_marker h _⟩
  simp only [List.length_append, List.length_cons, List.length_replicate]
  omega

/-- **Un-padding is polynomial-time**: `⟨s, v⟩ ↦ padDecode s v`.

**Proof sketch.** The catalog's marker strip maps `⟨s, v⟩` to `⟨s, u⟩` (or `[]` when `v`
has no `true`). If the result is a well-formed pair whose components have equal length,
output the second component `u`; if it is a pair of unequal lengths, output its first
component `s`; if the strip failed, output the first component of the original input.
Each test and branch is a catalog function, combined by polynomial-time branching. -/
theorem polyTimeComputable_padDecode :
    PolyTimeComputable (fun z => padDecode (pairFstD z) (pairSndD z)) := by
  classical
  let q : List Bool → List Bool := fun x => match pairDecode x with
    | some (a, v) =>
      match splitAtLastTrue v with
      | some u => pairEncode a u
      | none => []
    | none => []
  have hq : PolyTimeComputable q := by
    obtain ⟨M, c, hM⟩ := FinTM.computesFunInTime_stripLast
    exact ⟨M, c, 2, hM⟩
  have hvalid : PolyTimeComputable (fun x => [(pairDecode x).isSome]) :=
    polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid
  have h := polyTimeComputable_ite (hvalid.comp hq)
    (polyTimeComputable_ite (polyTimeComputable_lenEq.comp hq)
      (polyTimeComputable_pairSndD.comp hq) (polyTimeComputable_pairFstD.comp hq))
    polyTimeComputable_pairFstD
  convert h using 1
  funext z
  simp only [Function.comp_apply]
  cases hz : pairDecode z with
  | none =>
    have h1 : pairFstD z = [] := by simp [pairFstD, hz]
    have h2 : pairSndD z = [] := by simp [pairSndD, hz]
    have h3 : q z = [] := by simp [q, hz]
    simp [h1, h2, h3, padDecode, splitAtLastTrue, pairDecode]
  | some p =>
    obtain ⟨a, v⟩ := p
    have h1 : pairFstD z = a := by simp [pairFstD, hz]
    have h2 : pairSndD z = v := by simp [pairSndD, hz]
    rw [h1, h2]
    cases hs : splitAtLastTrue v with
    | none =>
      have h3 : q z = [] := by simp [q, hz, hs]
      simp [h3, padDecode, hs, pairDecode]
    | some u =>
      have h3 : q z = pairEncode a u := by simp [q, hz, hs]
      by_cases hu : u.length = a.length
      · simp [h3, padDecode, hs, pairDecode_pairEncode, hu]
      · have hu' : a.length ≠ u.length := fun h => hu h.symm
        simp [h3, padDecode, hs, pairDecode_pairEncode, hu, hu']

/-! ### Block-wise decoding of nested tuples -/

/-- **Block-wise decoding of a nested tuple.** With side information `s`,
`tupleDecode base dec n s` decodes the last `n` blocks of `⟨⋯⟨w, v₁⟩, …, vₙ⟩` with
`dec s` and the remaining prefix `w` with `base s`:
`tupleDecode base dec n s ⟨⋯⟨w, v₁⟩, …, vₙ⟩ = ⟨⋯⟨base s w, dec s v₁⟩, …, dec s vₙ⟩`. -/
def tupleDecode (base dec : List Bool → List Bool → List Bool) :
    ℕ → List Bool → List Bool → List Bool
  | 0, s, w => base s w
  | n + 1, s, z => pairEncode (tupleDecode base dec n s (pairFstD z)) (dec s (pairSndD z))

/-- Decoding one more block of a pair decodes its second component. -/
@[simp] theorem tupleDecode_succ_pairEncode (base dec : List Bool → List Bool → List Bool)
    (n : ℕ) (s w v : List Bool) :
    tupleDecode base dec (n + 1) s (pairEncode w v) =
      pairEncode (tupleDecode base dec n s w) (dec s v) := by
  simp [tupleDecode]

/-- **Block-wise decoding is polynomial-time** for every fixed depth `n`, as a function of
the pair `⟨s, z⟩`, provided the base decoder and the block decoder are.

**Proof sketch.** Induction on `n`: the depth-`(n+1)` decoder pairs the depth-`n` decoder
applied to `⟨s, fst z⟩` with the block decoder applied to `⟨s, snd z⟩`; both arguments
are pairings of projections, so pairing and composition closure apply. -/
theorem polyTimeComputable_tupleDecode {base dec : List Bool → List Bool → List Bool}
    (hbase : PolyTimeComputable (fun p => base (pairFstD p) (pairSndD p)))
    (hdec : PolyTimeComputable (fun p => dec (pairFstD p) (pairSndD p))) (n : ℕ) :
    PolyTimeComputable (fun p => tupleDecode base dec n (pairFstD p) (pairSndD p)) := by
  induction n with
  | zero => exact hbase
  | succ n ih =>
    have r1 : PolyTimeComputable (fun p => pairEncode (pairFstD p) (pairFstD (pairSndD p))) :=
      polyTimeComputable_pairFstD.pairEncode
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
    have r2 : PolyTimeComputable (fun p => pairEncode (pairFstD p) (pairSndD (pairSndD p))) :=
      polyTimeComputable_pairFstD.pairEncode
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
    convert (ih.comp r1).pairEncode (hdec.comp r2) using 1
    funext p
    simp [tupleDecode]

/-! ### Unary polynomial-time length functions -/

/-- `ℓ` is a **unary polynomial-time length function**: `y ↦ 1^{ℓ(y)}` is polynomial-time
computable. Such `ℓ` are polynomially bounded (`UnaryPT.bound`) and serve as the block
lengths of intermediate quantifier prefixes. -/
def UnaryPT (ℓ : List Bool → ℕ) : Prop :=
  PolyTimeComputable (fun y => List.replicate (ℓ y) true)

/-- A unary polynomial-time length function is polynomially bounded. -/
theorem UnaryPT.bound {ℓ : List Bool → ℕ} (h : UnaryPT ℓ) :
    ∃ A a : ℕ, ∀ y : List Bool, ℓ y ≤ A * (y.length + 1) ^ a := by
  obtain ⟨A, a, hA⟩ := PolyTimeComputable.output_length_le h
  exact ⟨A, a, fun y => by simpa using hA y⟩

/-- The explicit polynomial `C (|f y| + 1)^c` of the output length of a polynomial-time `f`
is a unary polynomial-time length function. -/
theorem unaryPT_poly (C c : ℕ) {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    UnaryPT (fun y => C * ((f y).length + 1) ^ c) := by
  have hu : PolyTimeComputable (fun x => List.replicate (C * (x.length + 1) ^ c) true) := by
    obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_polyUnary C c
    exact ⟨M, a, c + 1, hM⟩
  exact hu.comp hf

/-- Constant length functions are unary polynomial-time. -/
theorem unaryPT_const (k : ℕ) : UnaryPT (fun _ => k) :=
  polyTimeComputable_const _

/-- Unary polynomial-time length functions are closed under addition. -/
theorem UnaryPT.add {ℓ₁ ℓ₂ : List Bool → ℕ} (h₁ : UnaryPT ℓ₁) (h₂ : UnaryPT ℓ₂) :
    UnaryPT (fun y => ℓ₁ y + ℓ₂ y) := by
  unfold UnaryPT
  convert polyTimeComputable_pairConcat.comp (h₁.pairEncode h₂) using 1
  funext y
  simp

/-- Unary polynomial-time length functions are closed under precomposition with
polynomial-time functions. -/
theorem UnaryPT.comp {ℓ : List Bool → ℕ} {f : List Bool → List Bool} (h : UnaryPT ℓ)
    (hf : PolyTimeComputable f) : UnaryPT (fun y => ℓ (f y)) :=
  PolyTimeComputable.comp h hf

end Complexity.PolyHierarchy
