/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Params
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Degree
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The four JLS polynomial maps

## Main definitions

* `Params.halfForm` lifts one padded half of a multilinear monomial using tensor coordinates.
* `Params.G1`, `G2`, `G3` are the per-instance maps on structured seed coordinates.
* `Params.G4struct` adds the instances, and `G4` explicitly renames them to Fin coordinates.

## Main results

* `G1_eval` evaluates the lifted multilinear representation on the encoded vector.
* `G3_eval_of_scaled` implements flag multiplication through the precomputed private copy.
* `G4_degrees` bounds public degree by `d` and private degree by two.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026, Equation (2), p. 16, and
  Equations (3)-(4), p. 17.
* [PS10] R. Pass, A. Shelat, *A Course in Cryptography*, 2010, Definition 26.8.

**Deviations.** Dv3 transposes the LPN matrix. Dv6 uses composite polynomials with separate
public and private degrees. Dv10 uses degree `d` as in the formal construction on p. 17;
the overview's `d + 1` on p. 14 is not used. Dv15 transports structured coordinates by
explicit equivalences. The monomial support is sorted increasingly, padded with ones,
and split into two halves of length `D`; this fixes the paper's unspecified ordering.
The optional bucket positions contribute zero on overfull placements, including the
empty-grid boundary, as disclosed in `Buckets`. No efficiency claim is proved here.
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open scoped BigOperators

namespace Internal

/-- A monomial slot is the requested increasingly sorted support variable, or padding `none`
[JLS26, Equation (3), p. 17]. Multilinearity makes support enumeration the monomial's
variable list; padding stands for the constant one. No choice-based enumeration is used. -/
def monomialSlot {n : ℕ} (h : Fin n →₀ ℕ) (r : ℕ) : Option (Fin n) :=
  (h.support.sort (· ≤ ·))[r]?

/-- Monomial slots are indexed reads of the sorted finite support. Glue reader. -/
theorem monomialSlot_eq {n : ℕ} (h : Fin n →₀ ℕ) (r : ℕ) :
    monomialSlot h r = (h.support.sort (· ≤ ·))[r]? := rfl

/-- The two consecutive half-blocks contain at most all support variables
[JLS26, Equation (3), p. 17]. This is mathematical glue for the deterministic half split.

**Proof sketch.** The two ranges of list positions are disjoint; count their defined
entries and bound the result by `Finset.length_sort`. -/
theorem monomialSlot_two_halves_card_le {n : ℕ} (h : Fin n →₀ ℕ) (D : ℕ) :
    (Finset.univ.filter (fun r : Fin D => (monomialSlot h r.val).isSome)).card +
      (Finset.univ.filter (fun r : Fin D => (monomialSlot h (D + r.val)).isSome)).card ≤
        h.support.card := by
  classical
  let len := (h.support.sort (· ≤ ·)).length
  let A := Finset.univ.filter (fun r : Fin D => r.val < len)
  let C := Finset.univ.filter (fun r : Fin D => D + r.val < len)
  have hCinj : Function.Injective (fun r : Fin D => D + r.val) := ?_
  swap
  · intro r s hrs
    exact Fin.ext (Nat.add_left_cancel hrs)
  have hdisj : Disjoint (A.image (fun r => r.val)) (C.image (fun r => D + r.val)) := ?_
  swap
  · apply Finset.disjoint_left.mpr
    intro q hqA hqC
    obtain ⟨r, hr, hrq⟩ := Finset.mem_image.mp hqA
    obtain ⟨s, hs, hsq⟩ := Finset.mem_image.mp hqC
    have hrD := r.isLt
    omega
  have hsubset : A.image (fun r => r.val) ∪ C.image (fun r => D + r.val) ⊆
      Finset.range len := ?_
  swap
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
  have hbound := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective A Fin.val_injective,
    Finset.card_image_of_injective C hCinj, Finset.card_range] at hbound
  simp only [Internal.monomialSlot_eq, isSome_getElem?]
  change A.card + C.card ≤ h.support.card
  simpa only [len, Finset.length_sort] using hbound

end Internal

namespace Params

/-- Structured polynomial variables are public plus private coordinates,
`Var κ = Pub κ ⊕ Priv κ` [JLS26, SdSamp', p. 16]. Dv15 retains explicit coordinate types. -/
abbrev Var (P : Params) (κ : ℕ) : Type := P.Pub κ ⊕ P.Priv κ

/-- Structured variables are the public/private sum. Glue reader. -/
theorem var_eq (P : Params) (κ : ℕ) : P.Var κ = (P.Pub κ ⊕ P.Priv κ) := rfl

/-- Structured polynomials have coefficients in the input prime field,
`StructPoly κ pp = MvPolynomial (Var κ) (ZMod pp.p)`
[JLS26, Equations (3)-(4), p. 17]. Dv9 reads the prime from the public input. -/
abbrev StructPoly (P : Params) (κ : ℕ) (pp : PrimeParam κ) : Type :=
  MvPolynomial (P.Var κ) (ZMod pp.p)

/-- Structured polynomials are multivariate polynomials over the public prime. Glue reader. -/
theorem structPoly_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) :
    P.StructPoly κ pp = MvPolynomial (P.Var κ) (ZMod pp.p) := rfl

/-- An output index is transported along `m κ = G.outLen (n κ)`
[JLS26, §4 construction, p. 15]. This explicit cast avoids unfolding a foreign length. -/
def outputIndex (P : Params) (κ : ℕ) (j : Fin (P.m κ)) : Fin (P.G.outLen (P.n κ)) :=
  Fin.cast (P.m_eq κ) j

/-- Output-index transport is the cast along the published length equation. Glue reader. -/
theorem outputIndex_eq (P : Params) (κ : ℕ) (j : Fin (P.m κ)) :
    P.outputIndex κ j = Fin.cast (P.m_eq κ) j := rfl

/-- A public vector variable is the `i`th residue of instance `k`
[JLS26, SdSamp', p. 16]. Dv15 separates vector positions from the public error flag. -/
def bVar (P : Params) (κ : ℕ) (k : Fin κ) (i : Fin (P.n κ)) : P.Var κ :=
  .inl (.inl (k, i))

/-- A public vector variable is the nested left injection of its block and position. Glue. -/
theorem bVar_eq (P : Params) (κ : ℕ) (k : Fin κ) (i : Fin (P.n κ)) :
    P.bVar κ k i = Sum.inl (Sum.inl (k, i)) := rfl

/-- A private variable selects the original or precomputed flag-times-seed copy
[JLS26, SdSamp', p. 16]. `copy = true` selects flag*S, keeping final private degree two. -/
def sVar (P : Params) (κ : ℕ) (k : Fin κ) (copy : Bool) (v : P.SVar κ) : P.Var κ :=
  .inr (k, .inr (if copy then .inr v else .inl v))

/-- Private seed variables select one of the two explicit copies. Glue reader. -/
theorem sVar_eq (P : Params) (κ : ℕ) (k : Fin κ) (copy : Bool) (v : P.SVar κ) :
    P.sVar κ k copy v =
      Sum.inr (k, Sum.inr (if copy then Sum.inr v else Sum.inl v)) := rfl

/-- A left-factor coordinate is `(bucket, U(row,slot))`
[JLS26, Equation (2), p. 16]. Dv15 fixes the structured coordinate layout. -/
def uCoord (P : Params) (κ : ℕ) (b : Fin (P.B κ))
    (row : Fin (P.rc κ)) (r : Fin (P.t κ)) : P.SVar κ := .inr (b, .inl (row, r))

/-- Left-factor coordinates are the left branch of the bucket-factor component. Glue reader. -/
theorem uCoord_eq (P : Params) (κ : ℕ) (b : Fin (P.B κ))
    (row : Fin (P.rc κ)) (r : Fin (P.t κ)) :
    P.uCoord κ b row r = Sum.inr (b, Sum.inl (row, r)) := rfl

/-- A right-factor coordinate is `(bucket, V(slot,col))`
[JLS26, Equation (2), p. 16]. Dv15 fixes the structured coordinate layout. -/
def vCoord (P : Params) (κ : ℕ) (b : Fin (P.B κ))
    (r : Fin (P.t κ)) (col : Fin (P.rc κ)) : P.SVar κ := .inr (b, .inr (r, col))

/-- Right-factor coordinates are the right branch of the bucket-factor component. Glue reader. -/
theorem vCoord_eq (P : Params) (κ : ℕ) (b : Fin (P.B κ))
    (r : Fin (P.t κ)) (col : Fin (P.rc κ)) :
    P.vCoord κ b r col = Sum.inr (b, Sum.inr (r, col)) := rfl

/-- A lifted linear coefficient is `-A(i,a)` on secret coordinates and `b_i` on the final
coordinate, while padding selects only the final coordinate
[JLS26, Equation (3), p. 17]. Dv3 uses the transposed matrix; padding denotes one. -/
noncomputable def linearCoeff (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (slot : Option (Fin (P.n κ)))
    (a : Fin (P.ℓ κ + 1)) : P.StructPoly κ pp :=
  match slot with
  | none => if a.val = P.ℓ κ then 1 else 0
  | some i => if h : a.val < P.ℓ κ then
      MvPolynomial.C (-I'.2.2 i ⟨a.val, h⟩)
    else MvPolynomial.X (P.bVar κ k i)

/-- Lifted coefficients follow the secret/public split and the padding test. Glue reader. -/
theorem linearCoeff_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (slot : Option (Fin (P.n κ)))
    (a : Fin (P.ℓ κ + 1)) : P.linearCoeff κ pp I' k slot a =
      match slot with
      | none => if a.val = P.ℓ κ then 1 else 0
      | some i => if h : a.val < P.ℓ κ then
          MvPolynomial.C (-I'.2.2 i ⟨a.val, h⟩)
        else MvPolynomial.X (P.bVar κ k i) := rfl

/-- A half form sums tensor coefficients against the selected seed copy,
`∑ α, (∏ r, c(slot(offset+r),α_r)) X(S_copy(α))`
[JLS26, Equation (3), p. 17]. The deterministic padded split keeps each half linear
in private variables and uses at most the actual public variables in that half. -/
noncomputable def halfForm (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (h : Fin (P.n κ) →₀ ℕ)
    (offset : ℕ) (copy : Bool) : P.StructPoly κ pp :=
  ∑ α : Fin P.D → Fin (P.ℓ κ + 1),
    (∏ r : Fin P.D,
      P.linearCoeff κ pp I' k (Internal.monomialSlot h (offset + r.val)) (α r)) *
      MvPolynomial.X (P.sVar κ k copy (.inl α))

/-- Half forms are their explicit sum of tensor coefficients and seed coordinates. Glue reader. -/
theorem halfForm_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (h : Fin (P.n κ) →₀ ℕ)
    (offset : ℕ) (copy : Bool) : P.halfForm κ pp I' k h offset copy =
      ∑ α : Fin P.D → Fin (P.ℓ κ + 1),
        (∏ r : Fin P.D,
          P.linearCoeff κ pp I' k (Internal.monomialSlot h (offset + r.val)) (α r)) *
          MvPolynomial.X (P.sVar κ k copy (.inl α)) := rfl

/-- The lifted PRG polynomial pairs two padded tensor half forms with integer coefficients
[JLS26, Equation (3), p. 17]. `copy` changes only the first half's private coordinate;
this is the flag precomputation of Equation (4), without multiplying a cubic term. -/
noncomputable def prgPoly (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) (copy : Bool) : P.StructPoly κ pp :=
  ∑ h ∈ (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)).support,
    MvPolynomial.C ((MvPolynomial.coeff h
      (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) : ℤ) : ZMod pp.p) *
        P.halfForm κ pp I' k h 0 copy * P.halfForm κ pp I' k h P.D false

/-- The lifted PRG polynomial is the coefficient-weighted sum of two half forms. Glue reader. -/
theorem prgPoly_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) (copy : Bool) :
    P.prgPoly κ pp I' k j copy =
      ∑ h ∈ (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)).support,
        MvPolynomial.C ((MvPolynomial.coeff h
          (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) : ℤ) : ZMod pp.p) *
            P.halfForm κ pp I' k h 0 copy * P.halfForm κ pp I' k h P.D false := rfl

/-- The quadratic correction reads `U V` at the output's bucket position
[JLS26, Equation (3), p. 17]. The optional-position fallback is zero; `copy = true`
reads flag*U from the precomputed copy and leaves V unscaled. -/
noncomputable def correctionPoly (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) (copy : Bool) : P.StructPoly κ pp :=
  match Buckets.indexMap I'.2.1 (P.rc κ) j with
  | none => 0
  | some c => ∑ r : Fin (P.t κ),
      MvPolynomial.X (P.sVar κ k copy (P.uCoord κ (I'.2.1 j) c.1 r)) *
        MvPolynomial.X (P.sVar κ k false (P.vCoord κ (I'.2.1 j) r c.2))

/-- Quadratic corrections are the explicit factor-slot sum or zero for an absent position. Glue. -/
theorem correctionPoly_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) (copy : Bool) :
    P.correctionPoly κ pp I' k j copy =
      match Buckets.indexMap I'.2.1 (P.rc κ) j with
      | none => 0
      | some c => ∑ r : Fin (P.t κ),
          MvPolynomial.X (P.sVar κ k copy (P.uCoord κ (I'.2.1 j) c.1 r)) *
            MvPolynomial.X (P.sVar κ k false (P.vCoord κ (I'.2.1 j) r c.2)) := rfl

/-- The first map is the lifted PRG evaluation on the unscaled seed copy,
`G1 = prgPoly false` [JLS26, Equation (3), p. 17]. The padded half split specifies
how the stored degree-D tensor supplies both factors of each multilinear monomial. -/
noncomputable def G1 (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) : P.StructPoly κ pp :=
  P.prgPoly κ pp I' k j false

/-- The first map is the unscaled lifted polynomial. Glue reader. -/
theorem G1_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) :
    P.G1 κ pp I' k j = P.prgPoly κ pp I' k j false := rfl

/-- The second map adds the quadratic correction, `G2 = G1 + correctionPoly false`
[JLS26, Equation (3), p. 17]. Absent positions contribute zero only in the disclosed
failed-placement case. -/
noncomputable def G2 (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) : P.StructPoly κ pp :=
  P.G1 κ pp I' k j + P.correctionPoly κ pp I' k j false

/-- The second map adds the unscaled quadratic correction. Glue reader. -/
theorem G2_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) :
    P.G2 κ pp I' k j = P.G1 κ pp I' k j + P.correctionPoly κ pp I' k j false := rfl

/-- The third map scales each quadratic term's first private factor through flag*S,
`G3 = prgPoly true + correctionPoly true` [JLS26, Equation (4), p. 17]. Dv10 keeps
public degree d and private degree two; flag multiplication is precomputed in the seed. -/
noncomputable def G3 (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) : P.StructPoly κ pp :=
  P.prgPoly κ pp I' k j true + P.correctionPoly κ pp I' k j true

/-- The third map uses the flag-scaled copy in the first private factor. Glue reader. -/
theorem G3_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) :
    P.G3 κ pp I' k j =
      P.prgPoly κ pp I' k j true + P.correctionPoly κ pp I' k j true := rfl

/-- The structured fourth map sums the instance maps, `G4struct = ∑ k, G3_k`
[JLS26, Eval', p. 16]. The seed core selects at most one active flag. -/
noncomputable def G4struct (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (j : Fin (P.m κ)) : P.StructPoly κ pp :=
  ∑ k : Fin κ, P.G3 κ pp I' k j

/-- The structured fourth map is the instance sum. Glue reader. -/
theorem G4struct_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (j : Fin (P.m κ)) :
    P.G4struct κ pp I' j = ∑ k : Fin κ, P.G3 κ pp I' k j := rfl

/-- The fourth map renames structured variables by the explicit public/private equivalences
[JLS26, Eval', pp. 16-17]. Dv15 yields the Fin-indexed seed interface without any
choice of enumeration; Dv10 preserves degree d in public and degree two in private data. -/
noncomputable def G4 (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (j : Fin (P.m κ)) :
    MvPolynomial (Fin (P.pubLen κ) ⊕ Fin (P.privLen κ)) (ZMod pp.p) :=
  MvPolynomial.rename (Equiv.sumCongr (P.pubEquiv κ) (P.privEquiv κ))
    (P.G4struct κ pp I' j)

/-- The fourth map is renamed by the stated sum equivalence. Glue reader. -/
theorem G4_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (j : Fin (P.m κ)) :
    P.G4 κ pp I' j =
      MvPolynomial.rename (Equiv.sumCongr (P.pubEquiv κ) (P.privEquiv κ))
        (P.G4struct κ pp I' j) := rfl

/-- A half form's public degree is at most its number of unpadded slots
[JLS26, Equation (3), p. 17]. The padded split does not charge degree for constants.

**Proof sketch.** Bound each coefficient by its slot's zero-or-one contribution,
use the product bound, then the uniform sum bound. -/
theorem halfForm_pubDegree_le (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (h : Fin (P.n κ) →₀ ℕ)
    (offset : ℕ) (copy : Bool) :
    pubDegree (P.halfForm κ pp I' k h offset copy) ≤
      (Finset.univ.filter (fun r : Fin P.D =>
        (Internal.monomialSlot h (offset + r.val)).isSome)).card := by
  classical
  have hcoeff : ∀ (slot : Option (Fin (P.n κ))) (a : Fin (P.ℓ κ + 1)),
      pubDegree (P.linearCoeff κ pp I' k slot a) ≤ if slot.isSome then 1 else 0 := ?_
  swap
  · intro slot a
    cases slot with
    | none =>
      change pubDegree (P.linearCoeff κ pp I' k none a) ≤ 0
      rw [P.linearCoeff_eq]
      dsimp only
      split_ifs
      · have hc : pubDegree (1 : P.StructPoly κ pp) = 0 := ?_
        swap
        · simpa only [map_one] using
            (pubDegree_C (σ := P.Pub κ) (τ := P.Priv κ) (1 : ZMod pp.p))
        exact hc.le
      · exact pubDegree_zero.le
    | some i =>
      change pubDegree (P.linearCoeff κ pp I' k (some i) a) ≤ 1
      rw [P.linearCoeff_eq]
      dsimp only
      split_ifs
      · exact (pubDegree_C _).le.trans (Nat.zero_le 1)
      · rw [P.bVar_eq]
        exact pubDegree_X_inl _
  rw [P.halfForm_eq]
  apply pubDegree_finset_sum_le
  intro α hα
  have hprod := pubDegree_finset_prod_le (Finset.univ : Finset (Fin P.D))
    (fun r => P.linearCoeff κ pp I' k
      (Internal.monomialSlot h (offset + r.val)) (α r))
  have hnum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin P.D)))
    (fun r _ => hcoeff (Internal.monomialSlot h (offset + r.val)) (α r))
  rw [Finset.sum_boole] at hnum
  have hX : pubDegree
      (MvPolynomial.X (P.sVar κ k copy (.inl α)) : P.StructPoly κ pp) = 0 := ?_
  swap
  · rw [P.sVar_eq]
    exact pubDegree_X_inr _
  have hmul := pubDegree_mul_le
    (∏ r : Fin P.D,
      P.linearCoeff κ pp I' k (Internal.monomialSlot h (offset + r.val)) (α r))
    (MvPolynomial.X (P.sVar κ k copy (.inl α)))
  simpa only [hX, Nat.add_zero] using
    hmul.trans (Nat.add_le_add_right (hprod.trans hnum) _)

/-- A half form is linear in private coordinates, `privDegree halfForm ≤ 1`
[JLS26, Equation (3), p. 17]. Dv6 reads the degree on the composite polynomial.

**Proof sketch.** All coefficient factors contain only public variables; each term
contains exactly one private variable. Apply the degree sum and product bounds. -/
theorem halfForm_privDegree_le (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (h : Fin (P.n κ) →₀ ℕ)
    (offset : ℕ) (copy : Bool) : privDegree (P.halfForm κ pp I' k h offset copy) ≤ 1 := by
  classical
  have hcoeff : ∀ (slot : Option (Fin (P.n κ))) (a : Fin (P.ℓ κ + 1)),
      privDegree (P.linearCoeff κ pp I' k slot a) = 0 := ?_
  swap
  · intro slot a
    cases slot with
    | none =>
      rw [P.linearCoeff_eq]
      dsimp only
      split_ifs
      · simpa only [map_one] using
          (privDegree_C (σ := P.Pub κ) (τ := P.Priv κ) (1 : ZMod pp.p))
      · exact privDegree_zero
    | some i =>
      rw [P.linearCoeff_eq]
      dsimp only
      split_ifs
      · exact privDegree_C _
      · rw [P.bVar_eq]
        exact privDegree_X_inl _
  rw [P.halfForm_eq]
  apply privDegree_finset_sum_le
  intro α hα
  have hprod : privDegree (∏ r : Fin P.D,
      P.linearCoeff κ pp I' k (Internal.monomialSlot h (offset + r.val)) (α r)) ≤ 0 := ?_
  swap
  · have hp := privDegree_finset_prod_le (Finset.univ : Finset (Fin P.D))
      (fun r => P.linearCoeff κ pp I' k
        (Internal.monomialSlot h (offset + r.val)) (α r))
    simpa only [hcoeff, Finset.sum_const_zero] using hp
  have hX : privDegree
      (MvPolynomial.X (P.sVar κ k copy (.inl α)) : P.StructPoly κ pp) ≤ 1 := ?_
  swap
  · rw [P.sVar_eq]
    exact privDegree_X_inr _
  exact (privDegree_mul_le _ _).trans (Nat.add_le_add hprod hX)

/-- Either lifted PRG copy has public degree at most d and private degree at most two
[JLS26, Equation (3), p. 17]. The two half forms carry all variables of each monomial.

**Proof sketch.** Bound the combined unpadded slot count by support cardinality, use
multilinearity and the supplied total-degree bound, and sum the monomial bounds. -/
theorem prgPoly_degrees (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) (copy : Bool) :
    pubDegree (P.prgPoly κ pp I' k j copy) ≤ P.d ∧
      privDegree (P.prgPoly κ pp I' k j copy) ≤ 2 := by
  classical
  rw [P.prgPoly_eq]
  constructor
  · apply pubDegree_finset_sum_le
    intro h hh
    have hcard : h.support.card ≤ P.d := ?_
    swap
    · refine le_trans ?_ ((MvPolynomial.le_totalDegree hh).trans
        (P.R.totalDegree_poly_le (P.n κ) I'.1 (P.outputIndex κ j)))
      change h.support.card ≤ ∑ i ∈ h.support, h i
      simpa only [Nat.nsmul_eq_mul, Nat.mul_one] using
        (Finset.card_nsmul_le_sum h.support (fun i => h i) 1
          (fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)))
    have hc := pubDegree_C (σ := P.Pub κ) (τ := P.Priv κ)
      ((MvPolynomial.coeff h (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) : ℤ) : ZMod pp.p)
    have hl := P.halfForm_pubDegree_le κ pp I' k h 0 copy
    have hr := P.halfForm_pubDegree_le κ pp I' k h P.D false
    simp only [Nat.zero_add] at hl
    have hslots := Internal.monomialSlot_two_halves_card_le h P.D
    have hmul₁ := pubDegree_mul_le
      (MvPolynomial.C
        ((MvPolynomial.coeff h (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) : ℤ) : ZMod pp.p))
      (P.halfForm κ pp I' k h 0 copy)
    have hmul₂ := pubDegree_mul_le
      (MvPolynomial.C
        ((MvPolynomial.coeff h (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) : ℤ) : ZMod pp.p) *
          P.halfForm κ pp I' k h 0 copy)
      (P.halfForm κ pp I' k h P.D false)
    omega
  · apply privDegree_finset_sum_le
    intro h hh
    have hc := privDegree_C (σ := P.Pub κ) (τ := P.Priv κ)
      ((MvPolynomial.coeff h (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) : ℤ) : ZMod pp.p)
    have hl := P.halfForm_privDegree_le κ pp I' k h 0 copy
    have hr := P.halfForm_privDegree_le κ pp I' k h P.D false
    have hmul₁ := privDegree_mul_le
      (MvPolynomial.C
        ((MvPolynomial.coeff h (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) : ℤ) : ZMod pp.p))
      (P.halfForm κ pp I' k h 0 copy)
    have hmul₂ := privDegree_mul_le
      (MvPolynomial.C
        ((MvPolynomial.coeff h (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) : ℤ) : ZMod pp.p) *
          P.halfForm κ pp I' k h 0 copy)
      (P.halfForm κ pp I' k h P.D false)
    omega

/-- Quadratic corrections use no public variables and have private degree at most two
[JLS26, Equation (3), p. 17]. The scaled copy still represents just one private variable.

**Proof sketch.** Split the optional position, then bound each factor-slot product. -/
theorem correctionPoly_degrees (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) (copy : Bool) :
    pubDegree (P.correctionPoly κ pp I' k j copy) = 0 ∧
      privDegree (P.correctionPoly κ pp I' k j copy) ≤ 2 := by
  classical
  have hpX : ∀ (c : Bool) (v : P.SVar κ),
      pubDegree (MvPolynomial.X (P.sVar κ k c v) : P.StructPoly κ pp) = 0 := ?_
  swap
  · intro c v
    rw [P.sVar_eq]
    exact pubDegree_X_inr _
  have hsX : ∀ (c : Bool) (v : P.SVar κ),
      privDegree (MvPolynomial.X (P.sVar κ k c v) : P.StructPoly κ pp) ≤ 1 := ?_
  swap
  · intro c v
    rw [P.sVar_eq]
    exact privDegree_X_inr _
  rw [P.correctionPoly_eq]
  cases hpos : Buckets.indexMap I'.2.1 (P.rc κ) j with
  | none =>
    constructor
    · exact pubDegree_zero
    · rw [privDegree_zero]
      omega
  | some c =>
    constructor
    · apply Nat.eq_zero_of_le_zero
      apply pubDegree_finset_sum_le
      intro r hr
      simpa only [hpX, Nat.zero_add] using
        (pubDegree_mul_le (R := ZMod pp.p)
          (MvPolynomial.X (P.sVar κ k copy (P.uCoord κ (I'.2.1 j) c.1 r)))
          (MvPolynomial.X (P.sVar κ k false (P.vCoord κ (I'.2.1 j) r c.2))))
    · apply privDegree_finset_sum_le
      intro r hr
      exact (privDegree_mul_le _ _).trans
        (Nat.add_le_add (hsX copy _) (hsX false _))

/-- The third map has public degree at most d and private degree at most two
[JLS26, Equation (4), p. 17]. Dv10 uses the formal construction's degree d.

**Proof sketch.** Apply the lifted PRG and correction bounds and the sum bound. -/
theorem G3_degrees (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ)) :
    pubDegree (P.G3 κ pp I' k j) ≤ P.d ∧ privDegree (P.G3 κ pp I' k j) ≤ 2 := by
  have hp := P.prgPoly_degrees κ pp I' k j true
  have hc := P.correctionPoly_degrees κ pp I' k j true
  rw [P.G3_eq]
  constructor
  · exact (pubDegree_add_le _ _).trans
      (max_le hp.1 (hc.1.le.trans (Nat.zero_le P.d)))
  · exact (privDegree_add_le _ _).trans (max_le hp.2 hc.2)

/-- The final renamed map has public degree at most d and private degree at most two
[JLS26, Eval', pp. 16-17]. Dv10 and Dv15 preserve the formal degree through explicit renaming.

**Proof sketch.** Sum the instance degree bounds, then use the groupwise degree-renaming
lemmas backed by Mathlib's injective weighted-degree renaming theorem. -/
theorem G4_degrees (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (j : Fin (P.m κ)) :
    pubDegree (P.G4 κ pp I' j) ≤ P.d ∧ privDegree (P.G4 κ pp I' j) ≤ 2 := by
  rw [P.G4_eq]
  constructor
  · change pubDegree (MvPolynomial.rename
        (Sum.map (P.pubEquiv κ) (P.privEquiv κ)) (P.G4struct κ pp I' j)) ≤ P.d
    rw [pubDegree_rename, P.G4struct_eq]
    apply pubDegree_finset_sum_le Finset.univ _ P.d
    intro k _
    exact (P.G3_degrees κ pp I' k j).1
  · change privDegree (MvPolynomial.rename
        (Sum.map (P.pubEquiv κ) (P.privEquiv κ)) (P.G4struct κ pp I' j)) ≤ 2
    rw [privDegree_rename, P.G4struct_eq]
    apply privDegree_finset_sum_le Finset.univ _ 2
    intro k _
    exact (P.G3_degrees κ pp I' k j).2

/-- A tensor half form evaluates to the product of its encoded coordinates
[JLS26, Equation (3), p. 17]. Padding evaluates to one; the matrix is stored transposed.

**Proof sketch.** Use `Finset.prod_univ_sum` to expand a product of linear forms,
then evaluate the augmented secret against `(-A_i,b_i)` to obtain each `x_i`. -/
theorem halfForm_eval (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (h : Fin (P.n κ) →₀ ℕ) (offset : ℕ)
    (s : Fin (P.ℓ κ) → ZMod pp.p) (x : Fin (P.n κ) → ZMod pp.p)
    (z : P.Var κ → ZMod pp.p)
    (hpub : ∀ i, z (P.bVar κ k i) = (∑ a, I'.2.2 i a * s a) + x i)
    (htensor : ∀ α : Fin P.D → Fin (P.ℓ κ + 1),
      z (P.sVar κ k false (.inl α)) =
        ∏ r : Fin P.D, if ha : (α r).val < P.ℓ κ then s ⟨(α r).val, ha⟩ else 1) :
    MvPolynomial.eval z (P.halfForm κ pp I' k h offset false) =
      ∏ r : Fin P.D, match Internal.monomialSlot h (offset + r.val) with
        | none => 1
        | some i => x i := by
  classical
  let aug : Fin (P.ℓ κ + 1) → ZMod pp.p := fun a =>
    if ha : a.val < P.ℓ κ then s ⟨a.val, ha⟩ else 1
  have hT : ∀ α : Fin P.D → Fin (P.ℓ κ + 1),
      z (P.sVar κ k false (.inl α)) = ∏ r : Fin P.D, aug (α r) := htensor
  have hlin : ∀ slot : Option (Fin (P.n κ)),
      (∑ a : Fin (P.ℓ κ + 1),
        MvPolynomial.eval z (P.linearCoeff κ pp I' k slot a) * aug a) =
        match slot with
        | none => 1
        | some i => x i := ?_
  swap
  · intro slot
    cases slot with
    | none =>
      rw [Fin.sum_univ_castSucc]
      have hzero : ∀ a : Fin (P.ℓ κ),
          MvPolynomial.eval z (P.linearCoeff κ pp I' k none a.castSucc) *
            aug a.castSucc = 0 := ?_
      swap
      · intro a
        simp [P.linearCoeff_eq, aug, Nat.ne_of_lt a.isLt]
      simp_rw [hzero]
      simp [P.linearCoeff_eq, aug]
    | some i =>
      rw [Fin.sum_univ_castSucc]
      have hlow : ∀ a : Fin (P.ℓ κ),
          MvPolynomial.eval z (P.linearCoeff κ pp I' k (some i) a.castSucc) *
            aug a.castSucc = -(I'.2.2 i a * s a) := ?_
      swap
      · intro a
        simp [P.linearCoeff_eq, aug, a.isLt]
      have hlast :
          MvPolynomial.eval z (P.linearCoeff κ pp I' k (some i) (Fin.last (P.ℓ κ))) *
            aug (Fin.last (P.ℓ κ)) = z (P.bVar κ k i) := ?_
      swap
      · simp [P.linearCoeff_eq, aug]
      simp_rw [hlow]
      rw [hlast, Finset.sum_neg_distrib, hpub i]
      ring
  calc
    MvPolynomial.eval z (P.halfForm κ pp I' k h offset false) =
        ∑ α : Fin P.D → Fin (P.ℓ κ + 1),
          ∏ r : Fin P.D,
            MvPolynomial.eval z
                (P.linearCoeff κ pp I' k (Internal.monomialSlot h (offset + r.val))
                  (α r)) * aug (α r) := ?_
    _ = ∏ r : Fin P.D, ∑ a : Fin (P.ℓ κ + 1),
        MvPolynomial.eval z
            (P.linearCoeff κ pp I' k (Internal.monomialSlot h (offset + r.val)) a) *
          aug a :=
            (Fintype.prod_sum (fun (r : Fin P.D) (a : Fin (P.ℓ κ + 1)) =>
              MvPolynomial.eval z
                (P.linearCoeff κ pp I' k (Internal.monomialSlot h (offset + r.val)) a) *
                  aug a)).symm
    _ = ∏ r : Fin P.D, match Internal.monomialSlot h (offset + r.val) with
        | none => 1
        | some i => x i := ?_
  · rw [P.halfForm_eq, MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intro α hα
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_prod, MvPolynomial.eval_X, hT α,
      ← Finset.prod_mul_distrib]
  · apply Finset.prod_congr rfl
    intro r hr
    exact hlin _

/-- The first map evaluates the original integer PRG polynomial at the encoded vector
[JLS26, Equation (3), p. 17]. Dv3 uses the transposed matrix; the coefficients are cast
into the public prime field and the polynomial's multilinearity is supplied by Params.R.

**Proof sketch.** Evaluate both tensor half forms, join their padded products, and use
multilinearity to identify each support monomial with its original evaluation. -/
theorem G1_eval (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ))
    (s : Fin (P.ℓ κ) → ZMod pp.p) (x : Fin (P.n κ) → ZMod pp.p)
    (z : P.Var κ → ZMod pp.p)
    (hpub : ∀ i, z (P.bVar κ k i) = (∑ a, I'.2.2 i a * s a) + x i)
    (htensor : ∀ α : Fin P.D → Fin (P.ℓ κ + 1),
      z (P.sVar κ k false (.inl α)) =
        ∏ r : Fin P.D, if ha : (α r).val < P.ℓ κ then s ⟨(α r).val, ha⟩ else 1) :
    MvPolynomial.eval z (P.G1 κ pp I' k j) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod pp.p)) x
        (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) := by
  classical
  have hml := (MvPolynomial.mem_restrictDegree (Fin (P.n κ))
    (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)) 1).mp
      (P.R.poly_mem_restrictDegree (P.n κ) I'.1 (P.outputIndex κ j))
  have hmon : ∀ h ∈ (P.R.poly (P.n κ) I'.1 (P.outputIndex κ j)).support,
      (∏ r : Fin P.D, match Internal.monomialSlot h r.val with
        | none => 1
        | some i => x i) *
      (∏ r : Fin P.D, match Internal.monomialSlot h (P.D + r.val) with
        | none => 1
        | some i => x i) = ∏ i ∈ h.support, x i ^ h i := ?_
  swap
  · intro h hh
    have hexp : ∀ i ∈ h.support, h i = 1 := ?_
    swap
    · intro i hi
      have hle := hml h hh i
      have hne := Finsupp.mem_support_iff.mp hi
      omega
    have hsum : h.sum (fun _ e => e) = h.support.card := ?_
    swap
    · change Finset.sum h.support (fun i => h i) = h.support.card
      trans Finset.sum h.support (fun _ => 1)
      · exact Finset.sum_congr rfl hexp
      · simp
    have hcard : h.support.card ≤ P.d := ?_
    swap
    · have hd := (MvPolynomial.le_totalDegree hh).trans
        (P.R.totalDegree_poly_le (P.n κ) I'.1 (P.outputIndex κ j))
      rwa [hsum] at hd
    have hdouble : P.d ≤ P.D + P.D := ?_
    swap
    · rw [P.D_eq]
      omega
    let L := h.support.sort (· ≤ ·)
    let f : ℕ → ZMod pp.p := fun r => match L[r]? with
      | none => 1
      | some i => x i
    have hlen : L.length ≤ P.D + P.D := ?_
    swap
    · simpa only [L, Finset.length_sort] using hcard.trans hdouble
    have hjoin : (∏ r : Fin P.D, f r.val) *
        (∏ r : Fin P.D, f (P.D + r.val)) =
          ∏ r : Fin (P.D + P.D), f r.val := ?_
    swap
    · simpa only [Fin.coe_castAdd, Fin.coe_natAdd] using
        (Fin.prod_univ_add (fun r : Fin (P.D + P.D) => f r.val)).symm
    have hpadding : (∏ r : Fin (P.D + P.D), f r.val) =
        ∏ r : Fin L.length, f r.val := ?_
    swap
    · simp only [Fin.prod_univ_eq_prod_range]
      symm
      apply Finset.prod_subset (Finset.range_mono hlen)
      intro r hr hnot
      have hge : L.length ≤ r :=
        Nat.le_of_not_lt (fun hlt => hnot (Finset.mem_range.mpr hlt))
      simp only [f, List.getElem?_eq_none hge]
    have hlist : (∏ r : Fin L.length, f r.val) = Finset.prod h.support x := ?_
    swap
    · calc
        (∏ r : Fin L.length, f r.val) =
            ∏ r : Fin L.length, x L[r.val] := ?_
        _ = (L.map x).prod := Fin.prod_univ_fun_getElem L x
        _ = Finset.prod h.support x := ?_
      · apply Finset.prod_congr rfl
        intro r hr
        simp only [f, List.getElem?_eq_getElem r.isLt]
      · simpa only [L, Finset.sort_toFinset] using
          (List.prod_toFinset x (h.support.sort_nodup (· ≤ ·))).symm
    have hpow : (∏ i ∈ h.support, x i ^ h i) = Finset.prod h.support x := ?_
    swap
    · apply Finset.prod_congr rfl
      intro i hi
      rw [hexp i hi, pow_one]
    simp only [Internal.monomialSlot_eq]
    change (∏ r : Fin P.D, f r.val) * (∏ r : Fin P.D, f (P.D + r.val)) = _
    exact hjoin.trans (hpadding.trans (hlist.trans hpow.symm))
  rw [P.G1_eq, P.prgPoly_eq, MvPolynomial.eval_sum, MvPolynomial.eval₂_eq]
  apply Finset.sum_congr rfl
  intro h hh
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    P.halfForm_eval κ pp I' k h 0 s x z hpub htensor,
    P.halfForm_eval κ pp I' k h P.D s x z hpub htensor]
  simp only [Nat.zero_add]
  rw [mul_assoc, hmon h hh]
  rfl

/-- Precomputed private scaling makes the third map flag times the second map
[JLS26, Equation (4), p. 17]. Dv10 moves the scaling into one factor of every quadratic
term, retaining private degree two even when the flag is an arbitrary field element.

**Proof sketch.** Extract the common flag from each scaled tensor half and U coordinate,
then from each monomial and each factor-slot sum. -/
theorem G3_eval_of_scaled (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I' : P.Idx' κ pp) (k : Fin κ) (j : Fin (P.m κ))
    (z : P.Var κ → ZMod pp.p) (flag : ZMod pp.p)
    (hcopy : ∀ v : P.SVar κ, z (P.sVar κ k true v) = flag * z (P.sVar κ k false v)) :
    MvPolynomial.eval z (P.G3 κ pp I' k j) =
      flag * MvPolynomial.eval z (P.G2 κ pp I' k j) := by
  classical
  have hhalf : ∀ (h : Fin (P.n κ) →₀ ℕ) (offset : ℕ),
      MvPolynomial.eval z (P.halfForm κ pp I' k h offset true) =
        flag * MvPolynomial.eval z (P.halfForm κ pp I' k h offset false) := ?_
  swap
  · intro h offset
    simp only [P.halfForm_eq, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_prod, MvPolynomial.eval_X]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α hα
    rw [hcopy]
    ring
  have hprg : MvPolynomial.eval z (P.prgPoly κ pp I' k j true) =
      flag * MvPolynomial.eval z (P.prgPoly κ pp I' k j false) := ?_
  swap
  · simp only [P.prgPoly_eq, MvPolynomial.eval_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_C]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [hhalf]
    ring
  have hcorr : MvPolynomial.eval z (P.correctionPoly κ pp I' k j true) =
      flag * MvPolynomial.eval z (P.correctionPoly κ pp I' k j false) := ?_
  swap
  · rw [P.correctionPoly_eq, P.correctionPoly_eq]
    cases hpos : Buckets.indexMap I'.2.1 (P.rc κ) j with
    | none => simp
    | some c =>
      simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hcopy]
      ring
  rw [P.G3_eq, P.G2_eq, P.G1_eq, MvPolynomial.eval_add, MvPolynomial.eval_add,
    hprg, hcorr]
  ring

end Params

end TCSlib.Cryptography.Obfuscation.StructuredSeed
