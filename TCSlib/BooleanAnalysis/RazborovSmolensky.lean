/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.LowDegreeObstruction

open Finset
open scoped BigOperators

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ACP

section BooleanTransferAndFinalRoadmap

/-!
## Boolean transfer and final circuit lower-bound interfaces

The statements in this section connect the root-cube lower bound back to the
Boolean `MOD q` function.  The padding by `q - 1` Boolean variables is the
standard way to recover all residue classes from the zero-residue `MOD q`
predicate: to test residue `r`, fix a constant number of extra input bits to
shift the Hamming weight back to `0 mod q`.
-/

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Finite-field convenience instance for the chosen extension field. -/
noncomputable instance modqFieldFintype {q : ℕ} [Fact (Nat.Prime q)] :
    Fintype (ModqField (p := p) q) := by
  classical
  exact Fintype.ofFinite _

/-- Boolean inputs embedded into the root-of-unity cube by sending `0 ↦ 1` and
`1 ↦ ω`. -/
def boolToRootCube {K : Type*} [Field K]
    {n : ℕ} (ω : K) (x : Fin n → Fin 2) :
    rootCube ω n :=
  ⟨fun i => if x i = 0 then 1 else ω, by
    intro i
    by_cases h : x i = 0 <;> simp [h]⟩

/-- The product monomial on the root cube evaluates to `ω` raised to the
Boolean Hamming weight after the embedding `0 ↦ 1`, `1 ↦ ω`. -/
theorem boolToRootCube_rootProduct_eq_weightPow
    {K : Type*} [Field K]
    {n : ℕ} (ω : K) (x : Fin n → Fin 2) :
    (∏ i : Fin n, (boolToRootCube (K := K) ω x).1 i) =
      ω ^ ((Finset.univ : Finset (Fin n)).sum fun i => ((x i : Fin 2) : Nat)) := by
  classical
  let e : Fin n → ℕ := fun i => ((x i : Fin 2) : Nat)
  have hfactor : ∀ i : Fin n,
      (boolToRootCube (K := K) ω x).1 i = ω ^ e i := by
    intro i
    by_cases h0 : x i = 0
    · simp [boolToRootCube, e, h0]
    · have hval_ne_zero : ((x i : Fin 2) : Nat) ≠ 0 := by
        intro hval
        exact h0 (Fin.ext hval)
      have hval_lt_two : ((x i : Fin 2) : Nat) < 2 := (x i).isLt
      have hval_one : ((x i : Fin 2) : Nat) = 1 := by omega
      simp [boolToRootCube, e, h0, hval_one]
  have hprod_pow : ∀ s : Finset (Fin n),
      s.prod (fun i : Fin n => ω ^ e i) = ω ^ (s.sum fun i : Fin n => e i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        simp [ha, ih, pow_add]
  calc
    (∏ i : Fin n, (boolToRootCube (K := K) ω x).1 i)
        = ∏ i : Fin n, ω ^ e i := by simp [hfactor]
    _ = ω ^ ((Finset.univ : Finset (Fin n)).sum fun i => e i) :=
        hprod_pow (Finset.univ : Finset (Fin n))
    _ = ω ^ ((Finset.univ : Finset (Fin n)).sum fun i => ((x i : Fin 2) : Nat)) := by
        rfl


/-- Number of `ω`-coordinates of a root-cube point.  Under the Boolean
embedding `0 ↦ 1`, `1 ↦ ω`, this is the Boolean Hamming weight. -/
noncomputable def rootResidueWeight {K : Type*} [Field K]
    {n : ℕ} (ω : K) (x : rootCube ω n) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => x.1 i = ω)).card

/-- The residue-`r` indicator on the root cube, valued in the ambient field. -/
noncomputable def rootResidueIndicator {K : Type*} [Field K]
    {q n : ℕ} (ω : K) (r : Fin q) (x : rootCube ω n) : K := by
  classical
  exact if rootResidueWeight (K := K) (n := n) ω x % q = r.1 then 1 else 0

/-- Boolean Hamming weight, as a natural number. -/
def boolWeight {n : ℕ} (x : Fin n → Fin 2) : ℕ :=
  (Finset.univ : Finset (Fin n)).sum fun i => ((x i : Fin 2) : Nat)

/-- The Boolean residue-`r` indicator, valued in a field. -/
noncomputable def boolResidueIndicator {K : Type*} [Field K]
    {q n : ℕ} (r : Fin q) (x : Fin n → Fin 2) : K := by
  classical
  exact if boolWeight x % q = r.1 then 1 else 0


/-- Decode a root-cube coordinate as a Boolean bit.  When `ω ≠ 1`, this sends
`1 ↦ 0` and `ω ↦ 1` on the cube `{1,ω}`. -/
noncomputable def rootCubeBit {K : Type*} [Field K]
    {n : ℕ} (ω : K) (x : rootCube ω n) (i : Fin n) : Fin 2 := by
  classical
  exact if x.1 i = 1 then 0 else 1

/-- Number of padding `1` bits needed to turn residue `r` into residue `0`.
For `r = 0` this is `0`; for `r > 0` this is `q-r`, expressed uniformly as
`(q-r) mod q`. -/
def residuePadOnes {q : ℕ} (r : Fin q) : ℕ :=
  (q - r.1) % q

/-- The padded Boolean input associated to a root-cube point and a target
residue.  The first `n` bits are the decoded root-cube point; the final `q-1`
bits contain exactly `residuePadOnes r` many `1`s. -/
noncomputable def paddedResidueInput {K : Type*} [Field K]
    {q n : ℕ} (ω : K) (r : Fin q) (x : rootCube ω n) :
    Fin (n + (q - 1)) → Fin 2 := by
  classical
  intro j
  exact if hj : j.1 < n then
    rootCubeBit (K := K) (n := n) ω x ⟨j.1, hj⟩
  else if j.1 - n < residuePadOnes r then 1 else 0

/-- The affine polynomial which decodes a root-cube coordinate as a Boolean:
`1 ↦ 0` and `ω ↦ 1`. -/
noncomputable def rootAffineBoolPoly {K : Type*} [Field K]
    {n : ℕ} (ω : K) (i : Fin n) : MvPolynomial (Fin n) K :=
  MvPolynomial.C (ω - 1)⁻¹ * (MvPolynomial.X i - MvPolynomial.C 1)

/-- The affine Boolean decoder `x ↦ (x - 1)/(ω - 1)` has degree at most one. -/
theorem rootAffineBoolPoly_totalDegree_le_one {K : Type*} [Field K]
    {n : ℕ} (ω : K) (i : Fin n) :
    (rootAffineBoolPoly (K := K) (n := n) ω i).totalDegree ≤ 1 := by
  classical
  unfold rootAffineBoolPoly
  have hsub :
      (MvPolynomial.X i - MvPolynomial.C (1 : K) : MvPolynomial (Fin n) K).totalDegree ≤ 1 := by
    rw [sub_eq_add_neg]
    calc
      (MvPolynomial.X i + -MvPolynomial.C (1 : K) : MvPolynomial (Fin n) K).totalDegree
          ≤ max (MvPolynomial.X i : MvPolynomial (Fin n) K).totalDegree
              (-MvPolynomial.C (1 : K) : MvPolynomial (Fin n) K).totalDegree := by
                exact MvPolynomial.totalDegree_add _ _
      _ ≤ 1 := by
            simp
  calc
    (MvPolynomial.C (ω - 1)⁻¹ * (MvPolynomial.X i - MvPolynomial.C (1 : K)) :
        MvPolynomial (Fin n) K).totalDegree
        ≤ (MvPolynomial.C (ω - 1)⁻¹ : MvPolynomial (Fin n) K).totalDegree +
            (MvPolynomial.X i - MvPolynomial.C (1 : K) : MvPolynomial (Fin n) K).totalDegree := by
              exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + 1 := by
          exact Nat.add_le_add (by simp) hsub
    _ = 1 := by simp

/-- Variable substitution used to restrict a padded Boolean polynomial to the
root cube and to fix the padding bits for residue `r`. -/
noncomputable def paddedResidueSubst
    {q n : ℕ} [Fact (Nat.Prime q)]
    (ω : ModqField (p := p) q) (r : Fin q) :
    Fin (n + (q - 1)) → MvPolynomial (Fin n) (ModqField (p := p) q) := by
  classical
  intro j
  exact if hj : j.1 < n then
    rootAffineBoolPoly (K := ModqField (p := p) q) (n := n) ω ⟨j.1, hj⟩
  else if j.1 - n < residuePadOnes r then
    MvPolynomial.C 1
  else
    MvPolynomial.C 0

/-- Restrict a padded Boolean polynomial over `ZMod p` to the root cube over the
chosen extension field, fixing the padding variables according to residue `r`. -/
noncomputable def paddedResiduePolynomial
    {q n : ℕ} [Fact (Nat.Prime q)]
    (ω : ModqField (p := p) q) (r : Fin q)
    (P : MvPolynomial (Fin (n + (q - 1))) (ZMod p)) :
    MvPolynomial (Fin n) (ModqField (p := p) q) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : ModqField (p := p) q →+*
      MvPolynomial (Fin n) (ModqField (p := p) q))
    (paddedResidueSubst (p := p) (q := q) (n := n) ω r)
    ((MvPolynomial.map (algebraMap (ZMod p) (ModqField (p := p) q))) P)

/-- The affine restriction/fixing operation does not increase total degree. -/
theorem paddedResiduePolynomial_totalDegree_le
    {q n : ℕ} [Fact (Nat.Prime q)]
    (ω : ModqField (p := p) q) (r : Fin q)
    (P : MvPolynomial (Fin (n + (q - 1))) (ZMod p)) :
    (paddedResiduePolynomial (p := p) (q := q) (n := n) ω r P).totalDegree ≤
      P.totalDegree := by
  classical
  let K := ModqField (p := p) q
  let f : ZMod p →+* K := algebraMap (ZMod p) K
  let subst : Fin (n + (q - 1)) → MvPolynomial (Fin n) K :=
    paddedResidueSubst (p := p) (q := q) (n := n) ω r
  have hsubst_deg : ∀ j : Fin (n + (q - 1)), (subst j).totalDegree ≤ 1 := by
    intro j
    by_cases hj : j.1 < n
    · have hroot :=
        rootAffineBoolPoly_totalDegree_le_one
          (K := K) (n := n) ω ⟨j.1, hj⟩
      simpa [subst, paddedResidueSubst, hj] using hroot
    · by_cases hpad : j.1 - n < residuePadOnes r
      · simp [subst, paddedResidueSubst, hj, hpad]
      · simp [subst, paddedResidueSubst, hj, hpad]
  have hmap_expand :
      (MvPolynomial.map f P) =
        P.support.sum
          (fun m : Fin (n + (q - 1)) →₀ ℕ =>
            MvPolynomial.monomial m (f (MvPolynomial.coeff m P))) := by
    have hsupport :
        P.support.sum
            (fun m : Fin (n + (q - 1)) →₀ ℕ =>
              MvPolynomial.monomial m (MvPolynomial.coeff m P)) = P :=
      MvPolynomial.support_sum_monomial_coeff P
    calc
      MvPolynomial.map f P
          = MvPolynomial.map f
              (P.support.sum
                (fun m : Fin (n + (q - 1)) →₀ ℕ =>
                  MvPolynomial.monomial m (MvPolynomial.coeff m P))) := by
              rw [hsupport]
      _ = P.support.sum
          (fun m : Fin (n + (q - 1)) →₀ ℕ =>
            MvPolynomial.monomial m (f (MvPolynomial.coeff m P))) := by
              rw [map_sum]
              refine Finset.sum_congr rfl ?_
              intro m hm
              rw [MvPolynomial.map_monomial]
  have hQ_expand :
      paddedResiduePolynomial (p := p) (q := q) (n := n) ω r P =
        P.support.sum
          (fun m : Fin (n + (q - 1)) →₀ ℕ =>
            MvPolynomial.C (f (MvPolynomial.coeff m P)) *
              m.prod (fun j e => subst j ^ e)) := by
    unfold paddedResiduePolynomial
    change (MvPolynomial.eval₂Hom
        (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) subst)
      (MvPolynomial.map f P) = _
    rw [hmap_expand]
    simp only [map_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    simpa [subst] using
      (MvPolynomial.eval₂Hom_monomial
        (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) subst m
        (f (MvPolynomial.coeff m P)))
  rw [hQ_expand]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro m hm
  have hprod_deg :
      (m.prod (fun j e => subst j ^ e)).totalDegree ≤
        m.sum (fun _ e => e) := by
    change (m.support.prod
        (fun j : Fin (n + (q - 1)) => subst j ^ (m j))).totalDegree ≤
      m.sum (fun _ e => e)
    calc
      (m.support.prod
          (fun j : Fin (n + (q - 1)) => subst j ^ (m j))).totalDegree
          ≤ m.support.sum
              (fun j : Fin (n + (q - 1)) => (subst j ^ (m j)).totalDegree) := by
                simpa using
                  (MvPolynomial.totalDegree_finset_prod
                    (R := K) (σ := Fin n) m.support
                    (fun j : Fin (n + (q - 1)) => subst j ^ (m j)))
      _ ≤ m.support.sum (fun j : Fin (n + (q - 1)) => m j) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            calc
              (subst j ^ (m j)).totalDegree ≤ (m j) * (subst j).totalDegree := by
                    exact MvPolynomial.totalDegree_pow (subst j) (m j)
              _ ≤ (m j) * 1 := Nat.mul_le_mul_left (m j) (hsubst_deg j)
              _ = m j := by simp
      _ = m.sum (fun _ e => e) := by
            change m.support.sum (fun j : Fin (n + (q - 1)) => m j) =
              m.sum (fun _ e => e)
            rw [Finsupp.sum]
  calc
    (MvPolynomial.C (f (MvPolynomial.coeff m P)) * m.prod (fun j e => subst j ^ e) :
        MvPolynomial (Fin n) K).totalDegree
        ≤ (MvPolynomial.C (f (MvPolynomial.coeff m P)) : MvPolynomial (Fin n) K).totalDegree +
            (m.prod (fun j e => subst j ^ e)).totalDegree := by
              exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + m.sum (fun _ e => e) := by
          exact Nat.add_le_add (by simp) hprod_deg
    _ = m.sum (fun _ e => e) := by simp
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hm

/-- Evaluation of the restricted polynomial at a root-cube point is the same as
evaluating the original padded Boolean polynomial at the associated padded
Boolean input, then extending scalars from `ZMod p` to the root-of-unity field. -/
theorem paddedResiduePolynomial_eval_eq_map_eval
    {q n : ℕ} [Fact (Nat.Prime q)]
    (ω : ModqField (p := p) q) (hω1 : ω ≠ 1) (r : Fin q)
    (P : MvPolynomial (Fin (n + (q - 1))) (ZMod p))
    (x : rootCube ω n) :
    (paddedResiduePolynomial (p := p) (q := q) (n := n) ω r P).eval x.1 =
      algebraMap (ZMod p) (ModqField (p := p) q)
        (P.eval (boolInput (p := p)
          (paddedResidueInput (K := ModqField (p := p) q)
            (q := q) (n := n) ω r x))) := by
  classical
  let K := ModqField (p := p) q
  let y : Fin (n + (q - 1)) → Fin 2 :=
    paddedResidueInput (K := K) (q := q) (n := n) ω r x
  have hωm1 : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  have hInv : (ω - 1)⁻¹ * (ω - 1) = 1 := by
    rw [mul_comm]
    exact mul_inv_cancel₀ hωm1
  have hrootBit : ∀ i : Fin n,
      (MvPolynomial.eval x.1)
        (rootAffineBoolPoly (K := K) (n := n) ω i) =
        algebraMap (ZMod p) K
          ((((rootCubeBit (K := K) (n := n) ω x i : Fin 2) : Nat) : ZMod p)) := by
    intro i
    by_cases hx1 : x.1 i = 1
    · simp [rootAffineBoolPoly, rootCubeBit, boolInput, hx1]
    · have hxω : x.1 i = ω := by
        rcases x.2 i with h | h
        · exact absurd h hx1
        · exact h
      simp [rootAffineBoolPoly, rootCubeBit, boolInput, hx1, hxω, hω1]
      rw [MvPolynomial.eval_C]; exact hInv
  have hsubst : ∀ j : Fin (n + (q - 1)),
      (MvPolynomial.eval x.1)
        (paddedResidueSubst (p := p) (q := q) (n := n) ω r j) =
        algebraMap (ZMod p) K ((boolInput (p := p) y) j) := by
    intro j
    by_cases hj : j.1 < n
    · simpa [paddedResidueSubst, y, paddedResidueInput, boolInput, hj]
        using hrootBit ⟨j.1, hj⟩
    · by_cases hpad : j.1 - n < residuePadOnes r
      · simp [paddedResidueSubst, y, paddedResidueInput, boolInput, hj, hpad]
      · simp [paddedResidueSubst, y, paddedResidueInput, boolInput, hj, hpad]
  calc
    (paddedResiduePolynomial (p := p) (q := q) (n := n) ω r P).eval x.1
        = MvPolynomial.eval₂ (algebraMap (ZMod p) K)
            (fun j : Fin (n + (q - 1)) =>
              (MvPolynomial.eval x.1)
                (paddedResidueSubst (p := p) (q := q) (n := n) ω r j)) P := by
          change (MvPolynomial.eval x.1)
            (MvPolynomial.eval₂
              (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
              (paddedResidueSubst (p := p) (q := q) (n := n) ω r)
              ((MvPolynomial.map (algebraMap (ZMod p) K)) P)) = _
          have hC_id :
              ((MvPolynomial.eval x.1) : MvPolynomial (Fin n) K →+* K).comp
                (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) = RingHom.id K := by
            ext a
            simp
          rw [MvPolynomial.eval_eval₂]
          simp only [MvPolynomial.eval₂_map]
          rw [hC_id]
          simp
    _ = MvPolynomial.eval₂ (algebraMap (ZMod p) K)
            (fun j : Fin (n + (q - 1)) =>
              algebraMap (ZMod p) K ((boolInput (p := p) y) j)) P := by
          congr 1
          funext j
          exact hsubst j
    _ = algebraMap (ZMod p) K (P.eval (boolInput (p := p) y)) := by
          exact (MvPolynomial.eval₂_comp
            (algebraMap (ZMod p) K) (boolInput (p := p) y) P).symm

/-- The padded Boolean input for residue `r` has zero `MOD q` value exactly when
`x` has root-cube weight congruent to `r`. -/
theorem paddedResidueInput_modQTarget_eq_residueIndicator
    {q n : ℕ} [Fact (Nat.Prime q)]
    (ω : ModqField (p := p) q) (hω1 : ω ≠ 1) (r : Fin q)
    (x : rootCube ω n) :
    algebraMap (ZMod p) (ModqField (p := p) q)
      (modQTarget (p := p) (q := q) (n := n + (q - 1))
        (paddedResidueInput (K := ModqField (p := p) q)
          (q := q) (n := n) ω r x)) =
      rootResidueIndicator (K := ModqField (p := p) q)
        (q := q) (n := n) ω r x := by
  classical
  let K := ModqField (p := p) q
  let y : Fin (n + (q - 1)) → Fin 2 :=
    paddedResidueInput (K := K) (q := q) (n := n) ω r x
  let w : ℕ := rootResidueWeight (K := K) (n := n) ω x
  let pad : ℕ := residuePadOnes r
  have hq : Nat.Prime q := ‹Fact (Nat.Prime q)›.out
  have hqpos : 0 < q := hq.pos
  have hrootBitNat : ∀ i : Fin n,
      (((rootCubeBit (K := K) (n := n) ω x i : Fin 2) : Nat) : ZMod q) =
        if x.1 i = ω then (1 : ZMod q) else 0 := by
    intro i
    by_cases hxiω : x.1 i = ω
    · have hxi_ne_one : ¬ x.1 i = 1 := by
        intro hxi1
        exact hω1 (hxiω.symm.trans hxi1)
      simp [rootCubeBit, hxiω, hxi_ne_one, hω1]
    · have hxi1 : x.1 i = 1 := by
        rcases x.2 i with h | h
        · exact h
        · exact False.elim (hxiω h)
      have hone_ne_ω : ¬ (1 : K) = ω := by
        intro h
        exact hω1 h.symm
      simp [rootCubeBit, hxi1, hxiω, hone_ne_ω]
  have hfirstZ :
      (∑ i : Fin n,
        (((rootCubeBit (K := K) (n := n) ω x i : Fin 2) : Nat) : ZMod q)) =
        (w : ZMod q) := by
    unfold w rootResidueWeight
    calc
      (∑ i : Fin n,
        (((rootCubeBit (K := K) (n := n) ω x i : Fin 2) : Nat) : ZMod q))
          = ∑ i : Fin n, (if x.1 i = ω then (1 : ZMod q) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact hrootBitNat i
      _ = (((Finset.univ : Finset (Fin n)).filter
              (fun i : Fin n => x.1 i = ω)).sum (fun _ => (1 : ZMod q))) := by
              rw [Finset.sum_filter]
      _ = (((Finset.univ : Finset (Fin n)).filter
              (fun i : Fin n => x.1 i = ω)).card : ZMod q) := by
              simp
  have hpad_lt : pad < q := by
    unfold pad residuePadOnes
    exact Nat.mod_lt _ hqpos
  have hpad_le : pad ≤ q - 1 := by
    omega
  have htailCard :
      ((Finset.univ : Finset (Fin (q - 1))).filter
        (fun k : Fin (q - 1) => k.1 < pad)).card = pad := by
    let e : {k : Fin (q - 1) // k.1 < pad} ≃ Fin pad :=
      { toFun := fun a => ⟨a.1.1, a.2⟩
        invFun := fun b =>
          ⟨(⟨b.1, lt_of_lt_of_le b.2 hpad_le⟩ : Fin (q - 1)), b.2⟩
        left_inv := by
          intro a
          apply Subtype.ext
          apply Fin.ext
          rfl
        right_inv := by
          intro b
          apply Fin.ext
          rfl }
    have hsub :
        Fintype.card {k : Fin (q - 1) // k.1 < pad} =
          ((Finset.univ : Finset (Fin (q - 1))).filter
            (fun k : Fin (q - 1) => k.1 < pad)).card := by
      simpa using
        (Fintype.card_subtype (p := fun k : Fin (q - 1) => k.1 < pad))
    calc
      ((Finset.univ : Finset (Fin (q - 1))).filter
        (fun k : Fin (q - 1) => k.1 < pad)).card
          = Fintype.card {k : Fin (q - 1) // k.1 < pad} := hsub.symm
      _ = Fintype.card (Fin pad) := Fintype.card_congr e
      _ = pad := by simp
  have htailZ :
      (∑ k : Fin (q - 1),
        (((if k.1 < pad then (1 : Fin 2) else 0 : Fin 2) : Nat) : ZMod q)) =
        (pad : ZMod q) := by
    calc
      (∑ k : Fin (q - 1),
        (((if k.1 < pad then (1 : Fin 2) else 0 : Fin 2) : Nat) : ZMod q))
          = ∑ k : Fin (q - 1), (if k.1 < pad then (1 : ZMod q) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hkpad : k.1 < pad <;> simp [hkpad]
      _ = (((Finset.univ : Finset (Fin (q - 1))).filter
              (fun k : Fin (q - 1) => k.1 < pad)).sum (fun _ => (1 : ZMod q))) := by
              rw [Finset.sum_filter]
      _ = (((Finset.univ : Finset (Fin (q - 1))).filter
              (fun k : Fin (q - 1) => k.1 < pad)).card : ZMod q) := by
              simp
      _ = (pad : ZMod q) := by
              rw [htailCard]
  have hsumZ :
      (∑ j : Fin (n + (q - 1)), (((y j : Fin 2) : Nat) : ZMod q)) =
        ((w + pad : ℕ) : ZMod q) := by
    calc
      (∑ j : Fin (n + (q - 1)), (((y j : Fin 2) : Nat) : ZMod q))
          = (∑ i : Fin n,
              (((y (Fin.castAdd (q - 1) i) : Fin 2) : Nat) : ZMod q)) +
            (∑ k : Fin (q - 1),
              (((y (Fin.natAdd n k) : Fin 2) : Nat) : ZMod q)) := by
                exact Fin.sum_univ_add
                  (fun j : Fin (n + (q - 1)) => (((y j : Fin 2) : Nat) : ZMod q))
      _ = (∑ i : Fin n,
              (((rootCubeBit (K := K) (n := n) ω x i : Fin 2) : Nat) : ZMod q)) +
            (∑ k : Fin (q - 1),
              (((if k.1 < pad then (1 : Fin 2) else 0 : Fin 2) : Nat) : ZMod q)) := by
                congr 1
                · refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hj : (Fin.castAdd (q - 1) i).1 < n := i.2
                  simp [y, paddedResidueInput, hj]
                · refine Finset.sum_congr rfl ?_
                  intro k hk
                  have hj : ¬ (Fin.natAdd n k).1 < n := by
                    change ¬ (n + k.1 < n)
                    omega
                  have hsub : (Fin.natAdd n k).1 - n = k.1 := by simp [Fin.natAdd]
                  by_cases hkpad : k.1 < pad
                  · simp [y, paddedResidueInput, hj, hsub, pad, hkpad]
                  · simp [y, paddedResidueInput, hj, hsub, pad, hkpad]
      _ = (w : ZMod q) + (pad : ZMod q) := by
                rw [hfirstZ, htailZ]
      _ = ((w + pad : ℕ) : ZMod q) := by
                norm_num
  have hpad_mod : (w + pad) % q = 0 ↔ w % q = r.1 := by
    have hwr_lt : w % q < q := Nat.mod_lt w hqpos
    by_cases hr0 : r.1 = 0
    · have hpad0 : pad = 0 := by
        unfold pad residuePadOnes
        simp [hr0]
      simp [hpad0, hr0]
    · have hrpos : 0 < r.1 := Nat.pos_of_ne_zero hr0
      have hpad_eq : pad = q - r.1 := by
        unfold pad residuePadOnes
        have hlt : q - r.1 < q := by omega
        exact Nat.mod_eq_of_lt hlt
      have hpad_lt' : q - r.1 < q := by omega
      constructor
      · intro h
        have hzero : (w % q + (q - r.1)) % q = 0 := by
          calc
            (w % q + (q - r.1)) % q
                = (w % q + ((q - r.1) % q)) % q := by
                    rw [Nat.mod_eq_of_lt hpad_lt']
            _ = (w + (q - r.1)) % q := by
                    rw [← Nat.add_mod]
            _ = (w + pad) % q := by rw [hpad_eq]
            _ = 0 := h
        have hdiv : q ∣ w % q + (q - r.1) := by
          rw [Nat.dvd_iff_mod_eq_zero]
          exact hzero
        rcases hdiv with ⟨c, hc⟩
        have hsum_pos : 0 < w % q + (q - r.1) := by omega
        have hsum_lt : w % q + (q - r.1) < 2 * q := by omega
        have hc_pos : 0 < c := by
          by_contra hc0
          have hc_eq : c = 0 := Nat.eq_zero_of_not_pos hc0
          subst c
          simp at hc
          omega
        have hc_lt : c < 2 := by
          by_contra hc2
          have htwo_le : 2 ≤ c := Nat.le_of_not_gt hc2
          nlinarith [hc, hsum_lt, hqpos, htwo_le]
        have hc_eq_one : c = 1 := by omega
        rw [hc_eq_one] at hc
        omega
      · intro hwr
        rw [hpad_eq]
        calc
          (w + (q - r.1)) % q
              = (w % q + ((q - r.1) % q)) % q := by
                  rw [Nat.add_mod]
          _ = (r.1 + (q - r.1)) % q := by
                  rw [hwr, Nat.mod_eq_of_lt hpad_lt']
          _ = q % q := by
                  congr 1
                  omega
          _ = 0 := Nat.mod_self q
  have hzero_iff : (((w + pad : ℕ) : ZMod q) = 0) ↔ w % q = r.1 := by
    rw [ZMod.natCast_eq_zero_iff]
    rw [Nat.dvd_iff_mod_eq_zero]
    exact hpad_mod
  have hgate_iff :
      ((∑ j : Fin (n + (q - 1)), (((y j : Fin 2) : Nat) : ZMod q)) = 0) ↔
        w % q = r.1 := by
    rw [hsumZ]
    exact hzero_iff
  by_cases hres : w % q = r.1
  · have hzero : (∑ j : Fin (n + (q - 1)), (((y j : Fin 2) : Nat) : ZMod q)) = 0 :=
      hgate_iff.mpr hres
    have htarget :
        modQTarget (p := p) (q := q) (n := n + (q - 1))
          (paddedResidueInput (K := K) (q := q) (n := n) ω r x) = (1 : ZMod p) := by
      unfold modQTarget
      change
          ((((if (∑ j : Fin (n + (q - 1)), (((y j : Fin 2) : Nat) : ZMod q)) = 0
                then (1 : Fin 2) else (0 : Fin 2)) : Fin 2) : Nat) : ZMod p) = 1
      simp [y, hzero]
    have hind :
        rootResidueIndicator (K := K) (q := q) (n := n) ω r x = (1 : K) := by
      unfold rootResidueIndicator
      simp [w, hres]
    rw [htarget, hind]
    simp
  · have hnzero : ¬ (∑ j : Fin (n + (q - 1)), (((y j : Fin 2) : Nat) : ZMod q)) = 0 := by
      intro hzero
      exact hres (hgate_iff.mp hzero)
    have htarget :
        modQTarget (p := p) (q := q) (n := n + (q - 1))
          (paddedResidueInput (K := K) (q := q) (n := n) ω r x) = (0 : ZMod p) := by
      unfold modQTarget
      change
          ((((if (∑ j : Fin (n + (q - 1)), (((y j : Fin 2) : Nat) : ZMod q)) = 0
                then (1 : Fin 2) else (0 : Fin 2)) : Fin 2) : Nat) : ZMod p) = 0
      simp [y, hnzero]
    have hind :
        rootResidueIndicator (K := K) (q := q) (n := n) ω r x = (0 : K) := by
      unfold rootResidueIndicator
      simp [w, hres]
    rw [htarget, hind]
    simp

/-- For fixed residue padding, the map from the root cube to padded Boolean
inputs is injective. -/
theorem paddedResidueInput_injective
    {q n : ℕ} [Fact (Nat.Prime q)]
    (ω : ModqField (p := p) q) (hω1 : ω ≠ 1) (r : Fin q) :
    Function.Injective
      (paddedResidueInput (K := ModqField (p := p) q)
        (q := q) (n := n) ω r) := by
  classical
  intro x y hxy
  apply Subtype.ext
  funext i
  have hjBound : i.1 < n + (q - 1) :=
    lt_of_lt_of_le i.2 (Nat.le_add_right n (q - 1))
  let j : Fin (n + (q - 1)) := ⟨i.1, hjBound⟩
  have hjFirst : j.1 < n := i.2
  have hbit :
      rootCubeBit (K := ModqField (p := p) q) (n := n) ω x i =
        rootCubeBit (K := ModqField (p := p) q) (n := n) ω y i := by
    have h := congrFun hxy j
    simpa [paddedResidueInput, j, hjFirst] using h
  rcases x.2 i with hx1 | hxω
  · rcases y.2 i with hy1 | hyω
    · simpa [hx1, hy1]
    · have hy_ne_one : ¬ y.1 i = 1 := by
        intro hy1
        exact hω1 (hyω.symm.trans hy1)
      have h01 : (0 : Fin 2) = 1 := by
        simpa [rootCubeBit, hx1, hy_ne_one] using hbit
      exact False.elim (zero_ne_one h01)
  · rcases y.2 i with hy1 | hyω
    · have hx_ne_one : ¬ x.1 i = 1 := by
        intro hx1
        exact hω1 (hxω.symm.trans hx1)
      have h10 : (1 : Fin 2) = 0 := by
        simpa [rootCubeBit, hx_ne_one, hy1] using hbit
      exact False.elim (one_ne_zero h10)
    · simpa [hxω, hyω]

/-- First atomic Boolean-transfer obligation: from one padded zero-residue
`MOD q` approximant, obtain approximants for all residue classes on the
unpadded `n` variables, after extending coefficients from `ZMod p` to the chosen
root-of-unity field.

The proof now reduces the transfer to three remaining local lemmas above:
degree preservation under affine restriction, evaluation compatibility, and the
padding residue identity.  Injectivity of the root-cube-to-padded-Boolean map is
proved below. -/
theorem padded_modQ_approx_gives_root_residue_approximants
    {q n d E : ℕ} [Fact (Nat.Prime q)]
    (_hpq : p ≠ q)
    (ω : ModqField (p := p) q)
    (_hωq : ω ^ q = 1) (hω1 : ω ≠ 1)
    (P : MvPolynomial (Fin (n + (q - 1))) (ZMod p))
    (hPdeg : P.totalDegree ≤ d)
    (hPbad : badInputCount (p := p)
        (modQTarget (p := p) (q := q) (n := n + (q - 1))) P < E) :
    ∃ R : Fin q → MvPolynomial (Fin n) (ModqField (p := p) q),
      (∀ r : Fin q, (R r).totalDegree ≤ d) ∧
      (∀ r : Fin q,
        rootCubeBadCount (ω := ω)
          (rootResidueIndicator (K := ModqField (p := p) q)
            (q := q) (n := n) ω r) (R r) ≤ E) := by
  classical
  let R : Fin q → MvPolynomial (Fin n) (ModqField (p := p) q) :=
    fun r => paddedResiduePolynomial (p := p) (q := q) (n := n) ω r P
  refine ⟨R, ?_, ?_⟩
  · intro r
    exact le_trans
      (paddedResiduePolynomial_totalDegree_le
        (p := p) (q := q) (n := n) ω r P)
      hPdeg
  · intro r
    let A : Finset (rootCube ω n) :=
      Finset.univ.filter (fun x : rootCube ω n =>
        (R r).eval x.1 ≠
          rootResidueIndicator (K := ModqField (p := p) q)
            (q := q) (n := n) ω r x)
    let B : Finset (Fin (n + (q - 1)) → Fin 2) :=
      Finset.univ.filter (fun y : Fin (n + (q - 1)) → Fin 2 =>
        P.eval (boolInput (p := p) y) ≠
          modQTarget (p := p) (q := q) (n := n + (q - 1)) y)
    let emb : rootCube ω n ↪ (Fin (n + (q - 1)) → Fin 2) :=
      ⟨paddedResidueInput (K := ModqField (p := p) q)
          (q := q) (n := n) ω r,
        paddedResidueInput_injective (p := p) (q := q) (n := n) ω hω1 r⟩
    have hmap_subset : A.map emb ⊆ B := by
      intro y hy
      rcases Finset.mem_map.mp hy with ⟨x, hxA, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hgood
      have hgoodK := congrArg
        (algebraMap (ZMod p) (ModqField (p := p) q)) hgood
      have hxbad :
          (R r).eval x.1 ≠
            rootResidueIndicator (K := ModqField (p := p) q)
              (q := q) (n := n) ω r x := by
        exact (Finset.mem_filter.mp hxA).2
      have hcompat :
          (R r).eval x.1 =
            rootResidueIndicator (K := ModqField (p := p) q)
              (q := q) (n := n) ω r x := by
        calc
          (R r).eval x.1 =
              algebraMap (ZMod p) (ModqField (p := p) q)
                (P.eval (boolInput (p := p)
                  (paddedResidueInput (K := ModqField (p := p) q)
                    (q := q) (n := n) ω r x))) := by
                simpa [R] using
                  paddedResiduePolynomial_eval_eq_map_eval
                    (p := p) (q := q) (n := n) ω hω1 r P x
          _ = algebraMap (ZMod p) (ModqField (p := p) q)
                (modQTarget (p := p) (q := q) (n := n + (q - 1))
                  (paddedResidueInput (K := ModqField (p := p) q)
                    (q := q) (n := n) ω r x)) := hgoodK
          _ = rootResidueIndicator (K := ModqField (p := p) q)
                (q := q) (n := n) ω r x :=
                paddedResidueInput_modQTarget_eq_residueIndicator
                  (p := p) (q := q) (n := n) ω hω1 r x
      exact hxbad hcompat
    have hcardA_le_B : A.card ≤ B.card := by
      calc
        A.card = (A.map emb).card := by
          symm
          exact Finset.card_map _
        _ ≤ B.card := Finset.card_le_card hmap_subset
    have hB_lt : B.card < E := by
      simpa [B, badInputCount] using hPbad
    have hA_lt : A.card < E := lt_of_le_of_lt hcardA_le_B hB_lt
    have hA_eq :
        rootCubeBadCount (ω := ω)
          (rootResidueIndicator (K := ModqField (p := p) q)
            (q := q) (n := n) ω r) (R r) = A.card := by
      rfl
    rw [hA_eq]
    exact Nat.le_of_lt hA_lt
/-- Residue expansion of the root product.  On `{1,ω}^n`, the product
`∏ᵢ xᵢ` is `ω` to the number of `ω`-coordinates; since `ω^q = 1`, it only
depends on that number modulo `q`.  Thus it is the linear combination of the
residue indicators with coefficients `ω^r`.

This is a small algebraic/root-of-unity fact, independent of polynomial
approximation. -/
theorem rootProduct_eq_residueIndicator_sum
    {K : Type*} [Field K]
    {q n : ℕ} [Fact (Nat.Prime q)]
    (ω : K) (hωq : ω ^ q = 1) (x : rootCube ω n) :
    (∏ i : Fin n, x.1 i) =
      (Finset.univ : Finset (Fin q)).sum
        (fun r : Fin q =>
          ω ^ r.1 *
            rootResidueIndicator (K := K) (q := q) (n := n) ω r x) := by
  classical
  have hq : Nat.Prime q := ‹Fact (Nat.Prime q)›.out
  let w : ℕ := rootResidueWeight (K := K) (n := n) ω x
  have hprod_count : ∀ s : Finset (Fin n),
      s.prod (fun i : Fin n => x.1 i) =
        ω ^ ((s.filter (fun i : Fin n => x.1 i = ω)).card) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        by_cases haω : x.1 a = ω
        · have hnotmem : a ∉ s.filter (fun i : Fin n => x.1 i = ω) := by
            simp [ha]
          have hfilter :
              (insert a s).filter (fun i : Fin n => x.1 i = ω) =
                insert a (s.filter (fun i : Fin n => x.1 i = ω)) := by
            ext i
            by_cases hia : i = a
            · subst i
              simp [haω]
            · simp [hia]
          have hcard :
            ((insert a s).filter (fun i : Fin n => x.1 i = ω)).card =
              ((s.filter (fun i : Fin n => x.1 i = ω)).card).succ := by
            rw [hfilter]
            simp [hnotmem, Nat.succ_eq_add_one]
          calc
            (insert a s).prod (fun i : Fin n => x.1 i)
                = x.1 a * s.prod (fun i : Fin n => x.1 i) := by
                  simp [ha]
            _ = ω * ω ^ ((s.filter (fun i : Fin n => x.1 i = ω)).card) := by
                  rw [haω, ih]
            _ = ω ^ (((s.filter (fun i : Fin n => x.1 i = ω)).card).succ) := by
                  simpa [pow_succ, mul_comm]
            _ = ω ^ (((insert a s).filter (fun i : Fin n => x.1 i = ω)).card) := by
                  rw [hcard]
        · have ha1 : x.1 a = 1 := by
            rcases x.2 a with hxa | hxa
            · exact hxa
            · exact False.elim (haω hxa)
          have hfilter :
              (insert a s).filter (fun i : Fin n => x.1 i = ω) =
                s.filter (fun i : Fin n => x.1 i = ω) := by
            ext i
            by_cases hia : i = a
            · subst i
              simp [haω]
            · simp [hia]
          have hcard :
            ((insert a s).filter (fun i : Fin n => x.1 i = ω)).card =
              (s.filter (fun i : Fin n => x.1 i = ω)).card := by
            rw [hfilter]
          calc
            (insert a s).prod (fun i : Fin n => x.1 i)
                = x.1 a * s.prod (fun i : Fin n => x.1 i) := by
                  simp [ha]
            _ = 1 * ω ^ ((s.filter (fun i : Fin n => x.1 i = ω)).card) := by
                  rw [ha1, ih]
            _ = ω ^ ((s.filter (fun i : Fin n => x.1 i = ω)).card) := by
                  simp
            _ = ω ^ (((insert a s).filter (fun i : Fin n => x.1 i = ω)).card) := by
                  rw [hcard]
  have hprod_w : (∏ i : Fin n, x.1 i) = ω ^ w := by
    unfold w rootResidueWeight
    simpa using hprod_count (Finset.univ : Finset (Fin n))
  let r0 : Fin q := ⟨w % q, Nat.mod_lt w hq.pos⟩
  have hsum_residue :
      (Finset.univ : Finset (Fin q)).sum
        (fun r : Fin q =>
          ω ^ r.1 *
            rootResidueIndicator (K := K) (q := q) (n := n) ω r x) =
        ω ^ r0.1 := by
    have hsingle :
        (Finset.univ : Finset (Fin q)).sum
          (fun r : Fin q =>
            ω ^ r.1 *
              rootResidueIndicator (K := K) (q := q) (n := n) ω r x) =
          ω ^ r0.1 *
              rootResidueIndicator (K := K) (q := q) (n := n) ω r0 x := by
      refine Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset (Fin q)))
        (f := fun r : Fin q =>
          ω ^ r.1 *
            rootResidueIndicator (K := K) (q := q) (n := n) ω r x)
        (a := r0)
        (by simp)
        ?_
      intro r hr hrne
      have hne : rootResidueWeight (K := K) (n := n) ω x % q ≠ r.1 := by
        intro hwr
        apply hrne
        apply Fin.ext
        simpa [r0, w] using hwr.symm
      have hzero :
          rootResidueIndicator (K := K) (q := q) (n := n) ω r x = 0 := by
        unfold rootResidueIndicator
        exact if_neg hne
      simp [hzero]
    have hone :
        rootResidueIndicator (K := K) (q := q) (n := n) ω r0 x = 1 := by
      unfold rootResidueIndicator
      rw [if_pos]
      simp [r0, w]
    calc
      (Finset.univ : Finset (Fin q)).sum
          (fun r : Fin q =>
            ω ^ r.1 *
              rootResidueIndicator (K := K) (q := q) (n := n) ω r x)
          = ω ^ r0.1 *
              rootResidueIndicator (K := K) (q := q) (n := n) ω r0 x := hsingle
      _ = ω ^ r0.1 := by simp [hone]
  have hpow_mod : ω ^ w = ω ^ (w % q) := by
    have hw : w = q * (w / q) + w % q := by
      exact (Nat.div_add_mod w q).symm
    calc
      ω ^ w = ω ^ (q * (w / q) + w % q) := by
        conv_lhs => rw [hw]
      _ = ω ^ (q * (w / q)) * ω ^ (w % q) := by rw [pow_add]
      _ = (ω ^ q) ^ (w / q) * ω ^ (w % q) := by rw [pow_mul]
      _ = ω ^ (w % q) := by simp [hωq]
  calc
    (∏ i : Fin n, x.1 i) = ω ^ w := hprod_w
    _ = ω ^ (w % q) := hpow_mod
    _ = ω ^ r0.1 := rfl
    _ = (Finset.univ : Finset (Fin q)).sum
        (fun r : Fin q =>
          ω ^ r.1 *
            rootResidueIndicator (K := K) (q := q) (n := n) ω r x) := by
          rw [hsum_residue]

/-- Union-bound step for residue recombination.  If
`Q = ∑ᵣ ω^r Rᵣ`, then `Q` can be wrong on the root product only at points where
at least one residue approximant `Rᵣ` is wrong. -/
theorem rootCubeBadCount_residueCombination_le_sum
    {K : Type*} [Field K] [Finite K]
    {q n : ℕ} [Fact (Nat.Prime q)]
    (ω : K) (hωq : ω ^ q = 1)
    (R : Fin q → MvPolynomial (Fin n) K) :
    rootCubeBadCount (ω := ω)
      (fun x : rootCube ω n => ∏ i, x.1 i)
      ((Finset.univ : Finset (Fin q)).sum
        (fun r : Fin q => MvPolynomial.C (ω ^ r.1) * R r)) ≤
      (Finset.univ : Finset (Fin q)).sum
        (fun r : Fin q =>
          rootCubeBadCount (ω := ω)
            (rootResidueIndicator (K := K) (q := q) (n := n) ω r) (R r)) := by
  classical
  let Target : Finset (rootCube ω n) :=
    Finset.univ.filter (fun x : rootCube ω n =>
      (((Finset.univ : Finset (Fin q)).sum
        (fun r : Fin q => MvPolynomial.C (ω ^ r.1) * R r)).eval x.1) ≠
        (fun x : rootCube ω n => ∏ i, x.1 i) x)
  let Bad (r : Fin q) : Finset (rootCube ω n) :=
    Finset.univ.filter (fun x : rootCube ω n =>
      (R r).eval x.1 ≠
        rootResidueIndicator (K := K) (q := q) (n := n) ω r x)
  have hcover : Target ⊆ (Finset.univ : Finset (Fin q)).biUnion Bad := by
    intro x hx
    have hxbad :
        (((Finset.univ : Finset (Fin q)).sum
          (fun r : Fin q => MvPolynomial.C (ω ^ r.1) * R r)).eval x.1) ≠
          (∏ i : Fin n, x.1 i) := by
      simpa [Target] using (Finset.mem_filter.mp hx).2
    by_contra hnotmem
    have hgood : ∀ r : Fin q,
        (R r).eval x.1 =
          rootResidueIndicator (K := K) (q := q) (n := n) ω r x := by
      intro r
      by_contra hrbad
      have hxBad : x ∈ Bad r := by
        simp [Bad, hrbad]
      have hxUnion : x ∈ (Finset.univ : Finset (Fin q)).biUnion Bad := by
        exact Finset.mem_biUnion.mpr ⟨r, by simp, hxBad⟩
      exact hnotmem hxUnion
    have heval_sum :
        (((Finset.univ : Finset (Fin q)).sum
          (fun r : Fin q => MvPolynomial.C (ω ^ r.1) * R r)).eval x.1) =
          (Finset.univ : Finset (Fin q)).sum
            (fun r : Fin q =>
              ω ^ r.1 *
                rootResidueIndicator (K := K) (q := q) (n := n) ω r x) := by
      calc
        (((Finset.univ : Finset (Fin q)).sum
          (fun r : Fin q => MvPolynomial.C (ω ^ r.1) * R r)).eval x.1)
            = (Finset.univ : Finset (Fin q)).sum
                (fun r : Fin q => ω ^ r.1 * (R r).eval x.1) := by
                  simp [map_sum, map_mul]
        _ = (Finset.univ : Finset (Fin q)).sum
                (fun r : Fin q =>
                  ω ^ r.1 *
                    rootResidueIndicator (K := K) (q := q) (n := n) ω r x) := by
                  refine Finset.sum_congr rfl ?_
                  intro r hr
                  rw [hgood r]
    have htarget :
        (Finset.univ : Finset (Fin q)).sum
            (fun r : Fin q =>
              ω ^ r.1 *
                rootResidueIndicator (K := K) (q := q) (n := n) ω r x) =
          (∏ i : Fin n, x.1 i) := by
      exact (rootProduct_eq_residueIndicator_sum
        (K := K) (q := q) (n := n) ω hωq x).symm
    exact hxbad (by rw [heval_sum, htarget])
  have hcard_cover :
      Target.card ≤
        ((Finset.univ : Finset (Fin q)).biUnion Bad).card :=
    Finset.card_le_card hcover
  have hcard_union :
      ((Finset.univ : Finset (Fin q)).biUnion Bad).card ≤
        (Finset.univ : Finset (Fin q)).sum (fun r : Fin q => (Bad r).card) := by
    exact Finset.card_biUnion_le
  have htarget_card :
      rootCubeBadCount (ω := ω)
        (fun x : rootCube ω n => ∏ i, x.1 i)
        ((Finset.univ : Finset (Fin q)).sum
          (fun r : Fin q => MvPolynomial.C (ω ^ r.1) * R r)) = Target.card := by
    rfl
  have hbad_card :
      (Finset.univ : Finset (Fin q)).sum (fun r : Fin q => (Bad r).card) =
        (Finset.univ : Finset (Fin q)).sum
          (fun r : Fin q =>
            rootCubeBadCount (ω := ω)
              (rootResidueIndicator (K := K) (q := q) (n := n) ω r) (R r)) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    rfl
  calc
    rootCubeBadCount (ω := ω)
      (fun x : rootCube ω n => ∏ i, x.1 i)
      ((Finset.univ : Finset (Fin q)).sum
        (fun r : Fin q => MvPolynomial.C (ω ^ r.1) * R r))
        = Target.card := htarget_card
    _ ≤ ((Finset.univ : Finset (Fin q)).biUnion Bad).card := hcard_cover
    _ ≤ (Finset.univ : Finset (Fin q)).sum (fun r : Fin q => (Bad r).card) := hcard_union
    _ = (Finset.univ : Finset (Fin q)).sum
        (fun r : Fin q =>
          rootCubeBadCount (ω := ω)
            (rootResidueIndicator (K := K) (q := q) (n := n) ω r) (R r)) := hbad_card

/-- Second atomic Boolean-transfer obligation: combine residue-class
approximants into an approximant for the root product.  Algebraically this uses

`∏ᵢ xᵢ = ∑ r : Fin q, ω^r · 1_{wt(x) ≡ r (mod q)}`

on `{1,ω}^n`, and the error bound is the union bound over the `q` residue
approximants. -/
theorem root_residue_approximants_combine_to_rootProduct
    {K : Type*} [Field K] [Finite K]
    {q n d E : ℕ} [Fact (Nat.Prime q)]
    (ω : K) (hωq : ω ^ q = 1) (_hω1 : ω ≠ 1)
    (R : Fin q → MvPolynomial (Fin n) K)
    (hRdeg : ∀ r : Fin q, (R r).totalDegree ≤ d)
    (hRbad : ∀ r : Fin q,
      rootCubeBadCount (ω := ω)
        (rootResidueIndicator (K := K) (q := q) (n := n) ω r) (R r) ≤ E) :
    ∃ Q : MvPolynomial (Fin n) K,
      Q.totalDegree ≤ d ∧
      rootCubeBadCount (ω := ω)
        (fun x : rootCube ω n => ∏ i, x.1 i) Q ≤ q * E := by
  classical
  let Q : MvPolynomial (Fin n) K :=
    (Finset.univ : Finset (Fin q)).sum
      (fun r : Fin q => MvPolynomial.C (ω ^ r.1) * R r)
  refine ⟨Q, ?_, ?_⟩
  · unfold Q
    refine MvPolynomial.totalDegree_finsetSum_le
      (s := (Finset.univ : Finset (Fin q)))
      (f := fun r : Fin q => MvPolynomial.C (ω ^ r.1) * R r) ?_
    intro r hr
    calc
      (MvPolynomial.C (ω ^ r.1) * R r : MvPolynomial (Fin n) K).totalDegree
          ≤ (MvPolynomial.C (ω ^ r.1) : MvPolynomial (Fin n) K).totalDegree +
              (R r).totalDegree := by
                exact MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + d := by
          have hC0 :
              (MvPolynomial.C (ω ^ r.1) : MvPolynomial (Fin n) K).totalDegree = 0 := by
            exact MvPolynomial.totalDegree_C (σ := Fin n) (R := K) (ω ^ r.1)
          have hCle :
              ((MvPolynomial.C ω : MvPolynomial (Fin n) K) ^ r.1).totalDegree ≤ 0 := by
            simpa [map_pow] using (le_of_eq hC0)
          simpa [map_pow] using Nat.add_le_add hCle (hRdeg r)
      _ = d := by simp
  · calc
      rootCubeBadCount (ω := ω)
        (fun x : rootCube ω n => ∏ i, x.1 i) Q
          ≤ (Finset.univ : Finset (Fin q)).sum
              (fun r : Fin q =>
                rootCubeBadCount (ω := ω)
                  (rootResidueIndicator (K := K) (q := q) (n := n) ω r) (R r)) := by
                simpa [Q] using
                  rootCubeBadCount_residueCombination_le_sum
                    (K := K) (q := q) (n := n) ω hωq R
      _ ≤ (Finset.univ : Finset (Fin q)).sum (fun _ : Fin q => E) := by
                exact Finset.sum_le_sum (fun r hr => hRbad r)
      _ = q * E := by
                simp

/-- Sharp transfer theorem before the final monotonicity step: a too-good
low-degree approximant to padded Boolean `MOD q` over `𝔽_p` can be converted
into a degree-preserving approximant to the root product over
`𝔽_{p^(q-1)}`, with error at most `q * E`.

This is the remaining Boolean-transfer proof obligation.  It packages three
standard ingredients which will be formalized next:
* extend coefficients along `ZMod p → ModqField p q`;
* restrict the `q - 1` padded variables to constants to recover each residue
  class predicate from the zero-residue `MOD q` predicate;
* combine the `q` residue approximants as `∑ r, ω^r · 1_{|x| ≡ r}` and use a
  union bound over the `q` slices.
-/
theorem padded_modQ_approx_transfers_to_rootProduct_qE
    {q n d E : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    (ω : ModqField (p := p) q)
    (hωq : ω ^ q = 1) (hω1 : ω ≠ 1)
    (P : MvPolynomial (Fin (n + (q - 1))) (ZMod p))
    (hPdeg : P.totalDegree ≤ d)
    (hPbad : badInputCount (p := p)
        (modQTarget (p := p) (q := q) (n := n + (q - 1))) P < E) :
    ∃ Q : MvPolynomial (Fin n) (ModqField (p := p) q),
      Q.totalDegree ≤ d ∧
      rootCubeBadCount (ω := ω)
        (fun x : rootCube ω n => ∏ i, x.1 i) Q ≤ q * E := by
  classical
  rcases padded_modQ_approx_gives_root_residue_approximants
      (p := p) (q := q) (n := n) (d := d) (E := E)
      hpq ω hωq hω1 P hPdeg hPbad with
    ⟨R, hRdeg, hRbad⟩
  exact root_residue_approximants_combine_to_rootProduct
    (K := ModqField (p := p) q) (q := q) (n := n) (d := d) (E := E)
    ω hωq hω1 R hRdeg hRbad

/-- Transfer theorem: a too-good low-degree approximant to padded Boolean
`MOD q` over `𝔽_p` can be converted into a low-degree approximant to the root
product over `𝔽_{p^(q-1)}`.  The error worsens by at most a factor `q`, coming
from the union bound over the `q` residue classes.

This theorem is now just the sharp transfer theorem followed by monotonicity of
`≤` using the supplied ambient error bound `q * E ≤ e`. -/
theorem padded_modQ_approx_transfers_to_rootProduct
    {q n d E e : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    (ω : ModqField (p := p) q)
    (hωq : ω ^ q = 1) (hω1 : ω ≠ 1)
    (herror : q * E ≤ e)
    (P : MvPolynomial (Fin (n + (q - 1))) (ZMod p))
    (hPdeg : P.totalDegree ≤ d)
    (hPbad : badInputCount (p := p)
        (modQTarget (p := p) (q := q) (n := n + (q - 1))) P < E) :
    ∃ Q : MvPolynomial (Fin n) (ModqField (p := p) q),
      Q.totalDegree ≤ d ∧
      rootCubeBadCount (ω := ω)
        (fun x : rootCube ω n => ∏ i, x.1 i) Q ≤ e := by
  classical
  rcases padded_modQ_approx_transfers_to_rootProduct_qE
      (p := p) (q := q) (n := n) (d := d) (E := E)
      hpq ω hωq hω1 P hPdeg hPbad with
    ⟨Q, hQdeg, hQbad⟩
  exact ⟨Q, hQdeg, le_trans hQbad herror⟩

/-- Root-product inapproximability implies a Boolean low-degree lower bound for
padded `MOD q`. -/
theorem modQ_lowDegreeBadCountLB_from_rootProduct
    {q n d E e : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    (ω : ModqField (p := p) q)
    (hωq : ω ^ q = 1) (hω1 : ω ≠ 1)
    (herror : q * E ≤ e)
    (hroot :
      ¬ ∃ Q : MvPolynomial (Fin n) (ModqField (p := p) q),
          Q.totalDegree ≤ d ∧
          rootCubeBadCount (ω := ω)
            (fun x : rootCube ω n => ∏ i, x.1 i) Q ≤ e) :
    LowDegreeBadCountLB (p := p)
      (modQTarget (p := p) (q := q) (n := n + (q - 1))) d E := by
  classical
  unfold LowDegreeBadCountLB
  intro P hPdeg
  by_contra hnot
  have hPbad : badInputCount (p := p)
      (modQTarget (p := p) (q := q) (n := n + (q - 1))) P < E :=
    not_le.mp hnot
  rcases padded_modQ_approx_transfers_to_rootProduct
      (p := p) (q := q) (n := n) (d := d) (E := E) (e := e)
      hpq ω hωq hω1 herror P hPdeg hPbad with
    ⟨Q, hQdeg, hQbad⟩
  exact hroot ⟨Q, hQdeg, hQbad⟩

/-- Smolensky's low-degree lower bound for Boolean `MOD q`, packaged in the
exact `LowDegreeBadCountLB` interface needed by the circuit side.  This theorem
is obtained by choosing the nontrivial `q`-th root in `ModqField`, proving the
root-product lower bound by counting, and applying the Boolean transfer lemma. -/
theorem smolensky_modQ_lowDegreeBadCountLB
    {q n d E e B : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    (herror : q * E ≤ e)
    (hballB :
      (Finset.range (e + 1)).sum
        (fun t : ℕ =>
          Nat.choose (2 ^ n) t *
            Fintype.card (ModqField (p := p) q) ^ t) ≤ B)
    (hstrict :
      Fintype.card (ModqField (p := p) q) ^ (2 ^ n) >
        Fintype.card (LowDegreeSupport n (n / 2 + d) → ModqField (p := p) q) * B) :
    LowDegreeBadCountLB (p := p)
      (modQTarget (p := p) (q := q) (n := n + (q - 1))) d E := by
  classical
  rcases exists_nontrivial_qth_root_modqField (p := p) (q := q) hpq with
    ⟨ω, hωq, hω1⟩
  have hq : Nat.Prime q := ‹Fact (Nat.Prime q)›.out
  have hω0 : ω ≠ 0 := by
    intro h0
    have hqne0 : q ≠ 0 := Nat.ne_of_gt hq.pos
    have hzero : ω ^ q = 0 := by
      simpa [h0, hqne0]
    have h01 : (0 : ModqField (p := p) q) = 1 := by
      rw [← hzero, hωq]
    exact zero_ne_one h01
  have hroot :
      ¬ ∃ Q : MvPolynomial (Fin n) (ModqField (p := p) q),
          Q.totalDegree ≤ d ∧
          rootCubeBadCount (ω := ω)
            (fun x : rootCube ω n => ∏ i, x.1 i) Q ≤ e :=
    no_low_degree_rootProd_approx_concrete
      (K := ModqField (p := p) q) (ω := ω)
      (n := n) (d := d) (e := e) (B := B)
      hω0 hω1 hballB hstrict
  exact modQ_lowDegreeBadCountLB_from_rootProduct
    (p := p) (q := q) (n := n) (d := d) (E := E) (e := e)
    hpq ω hωq hω1 herror hroot

/-- Quantitative final form of `MOD q ∉ AC⁰[p]`: every `AC⁰[p]` circuit that
computes padded `MOD q` has size at least the lower bound delivered by the
Razborov--Smolensky approximation/counting argument.

The parameter `ℓ` is the randomness/accuracy parameter in the existing
AC⁰[p]-approximation theorem.  In the asymptotic corollary, one chooses `ℓ` as
a suitable power of `n` so that `circuitDegreeBound p ℓ F.depth` is below the
Smolensky threshold. -/
theorem MODq_notin_AC0p_quantitative
    {q n δ ℓ e B : ℕ} [Fact (Nat.Prime q)]
    (hpq : p ≠ q)
    {out : Type}
    (F : FeedForward (Fin 2) (Fin (n + (q - 1))) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACp_GateOps p))
    (hCompute : ∀ x : Fin (n + (q - 1)) → Fin 2,
      F.eval₁ x = (modGateOp q (n + (q - 1))).func x)
    (herror : q * (δ * 2 ^ (n + (q - 1))) ≤ e)
    (hballB :
      (Finset.range (e + 1)).sum
        (fun t : ℕ =>
          Nat.choose (2 ^ n) t *
            Fintype.card (ModqField (p := p) q) ^ t) ≤ B)
    (hstrict :
      Fintype.card (ModqField (p := p) q) ^ (2 ^ n) >
        Fintype.card
          (LowDegreeSupport n
            (n / 2 + circuitDegreeBound p ℓ F.depth) →
            ModqField (p := p) q) * B) :
    δ * 2 ^ ℓ ≤ F.size := by
  classical
  have hLB : LowDegreeBadCountLB (p := p)
      (modQTarget (p := p) (q := q) (n := n + (q - 1)))
      (circuitDegreeBound p ℓ F.depth) (δ * 2 ^ (n + (q - 1))) :=
    smolensky_modQ_lowDegreeBadCountLB
      (p := p) (q := q) (n := n)
      (d := circuitDegreeBound p ℓ F.depth)
      (E := δ * 2 ^ (n + (q - 1))) (e := e) (B := B)
      hpq herror hballB hstrict
  exact size_lower_bound_from_relative_badCountLB
    (p := p) (q := q) (n := n + (q - 1)) (δ := δ)
    F hUses hCompute ℓ hLB

end BooleanTransferAndFinalRoadmap

end ACP
