/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Matrix
import TCSlib.Cryptography.LWE.Experiments
import TCSlib.Cryptography.OneWayFunctions.Basic

import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concealer security: independent-secret column hybrids

## Main definitions

* `concealedSampler`: choose one public matrix and independent secrets for its concealed columns.
* `columnHybrid`, `columnTest`: replace one column at a time using a standard DLWE challenge.
* `shiftedSampler`: add a fixed public matrix, covering gadget and branch-key shifts.

## Main results

The concealed sampler's advantage is bounded by the sum of standard DLWE advantages
for its columns. Two fixed public shifts cost two such sums. These finite bounds
use independent seeds for the hidden columns and the original common public matrix.

## References

* [PW10] C. Peikert, B. Waters, *Lossy Trapdoor Functions and Their Applications*,
  author version 4 June 2010, Section 6.2, printed pages 33--34.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.3.

Every column uses `P.samples` rows under its own full uniform secret. Columns share
the matrix but have independent secret and noise seeds. This never substitutes
`P.samples*w` rows under one common secret or silently strengthens `DLWEAssumption`.
The actual finite-noise law is retained. No search, SIS or worst-case bridge is used.
-/

namespace TCSlib.Cryptography.TrapdoorFunctions.Lossy

open LWE (Parameters Noise)

/-- Sample a concealed matrix with independent secret/noise columns and one common
public matrix [PW10, Section 6.2, transposed convention]. -/
@[simps! (config := { isSimp := false }) fst snd]
def concealedSampler (P : Parameters) (χ : Noise) (w : ℕ)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → Fin w → χ.Coins))) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      Matrix (Fin P.samples) (Fin w) (ZMod P.modulus) :=
  (r.1, conceal r.1 r.2.1 (fun i j => χ.sample (r.2.2 i j)))

/-- The complete sampler uses the original integer-noise seeds in every concealed entry. -/
theorem concealedSampler_eq (P : Parameters) (χ : Noise) (w : ℕ)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → Fin w → χ.Coins))) :
    concealedSampler P χ w r =
      (r.1, conceal r.1 r.2.1 (fun i j => χ.sample (r.2.2 i j))) := rfl

/-- Column `j` of the concealed block is the existing common-secret LWE value vector.

**Proof sketch.** Read `conceal_eq`, public matrix product entries and
`LWE.noisyValues_apply`. The row secret of `T` supplies exactly this column's secret. -/
theorem conceal_column (P : Parameters) (χ : Noise) (w : ℕ)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (T : Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus))
    (η : (Fin P.samples → Fin w → χ.Coins)) (i : Fin P.samples) (j : Fin w) :
    conceal A T (fun i j => χ.sample (η i j)) i j =
      LWE.noisyValues P A (T j) (fun i => χ.sample (η i j)) i := by
  rw [conceal_eq, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply, LWE.noisyValues_apply]
  simp only [Matrix.transpose_apply]

/-- The first `k` concealed columns are real; all remaining columns are independently
uniform [PW10, Section 6.2, explicit hybrid convention]. -/
@[simps! (config := { isSimp := false }) fst snd]
def columnHybrid (P : Parameters) (χ : Noise) (w k : ℕ)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus) ×
        ((Fin P.samples → Fin w → χ.Coins) ×
          Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)))) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      Matrix (Fin P.samples) (Fin w) (ZMod P.modulus) :=
  (r.1, Matrix.of (fun i j => if j.val < k then
    LWE.noisyValues P r.1 (r.2.1 j) (fun i => χ.sample (r.2.2.1 i j)) i
    else r.2.2.2 i j))

/-- The complete hybrid retains the public matrix and selects real columns by `j<k`. -/
theorem columnHybrid_eq (P : Parameters) (χ : Noise) (w k : ℕ)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus) ×
        ((Fin P.samples → Fin w → χ.Coins) ×
          Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)))) :
    columnHybrid P χ w k r =
      (r.1, Matrix.of (fun i j => if j.val < k then
        LWE.noisyValues P r.1 (r.2.1 j) (fun i => χ.sample (r.2.2.1 i j)) i
        else r.2.2.2 i j)) := rfl

/-- Insert a standard DLWE challenge as column `k`, simulating earlier real and later
uniform columns with independent coins [PW10, Section 6.2]. -/
def columnTest {ρ : Type*} (P : Parameters) (χ : Noise) (w : ℕ) (k : Fin w)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)) → ρ → Bool)
    (c : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus))
    (r : Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.samples → Fin w → χ.Coins) ×
        (Matrix (Fin P.samples) (Fin w) (ZMod P.modulus) × ρ))) : Bool :=
  D (c.1, Matrix.of (fun i j => if j = k then c.2 i else if j.val < k.val then
    LWE.noisyValues P c.1 (r.1 j) (fun i => χ.sample (r.2.1 i j)) i
    else r.2.2.1 i j)) r.2.2.2

/-- The complete column test uses the challenge only in its designated column. -/
theorem columnTest_eq {ρ : Type*} (P : Parameters) (χ : Noise) (w : ℕ) (k : Fin w)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)) → ρ → Bool)
    (c : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus))
    (r : Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.samples → Fin w → χ.Coins) ×
        (Matrix (Fin P.samples) (Fin w) (ZMod P.modulus) × ρ))) :
    columnTest P χ w k D c r =
      D (c.1, Matrix.of (fun i j => if j = k then c.2 i else if j.val < k.val then
        LWE.noisyValues P c.1 (r.1 j) (fun i => χ.sample (r.2.1 i j)) i
        else r.2.2.1 i j)) r.2.2.2 := rfl

/-- A neighboring column-hybrid gap equals the standard DLWE advantage of its column test.

**Proof sketch.** Group the independent seeds by column. Use uniform-coordinate
replacement to plant the real challenge's secret and row noises in column `k`, or to
plant the ideal challenge's value vector there. The public matrix and test coins stay
fixed in each relabelling. The inserted columns give the two neighbouring hybrids. -/
theorem column_gap {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : Noise) (w : ℕ) (k : Fin w)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)) → ρ → Bool) :
    distAdv (columnHybrid P χ w (k.val + 1)) (columnHybrid P χ w k.val) D =
      LWE.decisionAdvantage P χ (columnTest P χ w k D) := by
  classical
  let Public := Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus)
  let Values := Fin P.samples → ZMod P.modulus
  let Real := (Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins)
  let Secrets := Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus)
  let Errors := Fin P.samples → Fin w → χ.Coins
  let Uniform := Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)
  let Hybrid := (Fin w → Real) × (Public × ((Fin w → Values) × ρ))
  let Ideal := (Fin w → Values) × (Public × ((Fin w → Real) × ρ))
  let Test := Secrets × (Errors × (Uniform × ρ))
  let event (t : ℕ) (A : Public) (real : Fin w → Real) (ideal : Fin w → Values)
      (r : ρ) : Prop :=
    D (columnHybrid P χ w t
      (A, ((fun j => (real j).1), ((fun i j => (real j).2 i), (fun i j => ideal j i))))) r = true
  -- Group the independent coins by column, without changing the public matrix or test coins.
  let hybridGroup : (Public × (Secrets × (Errors × Uniform))) × ρ ≃ Hybrid :=
    ⟨fun z => ((fun j => (z.1.2.1 j, fun i => z.1.2.2.1 i j)),
      (z.1.1, ((fun j i => z.1.2.2.2 i j), z.2))),
      fun z => ((z.2.1, ((fun j => (z.1 j).1),
        ((fun i j => (z.1 j).2 i), (fun i j => z.2.2.1 j i)))), z.2.2.2),
      fun _ => rfl, fun _ => rfl⟩
  let swap : Hybrid ≃ Ideal :=
    ⟨fun z => (z.2.2.1, (z.2.1, (z.1, z.2.2.2))),
      fun z => (z.2.2.1, (z.2.1, (z.1, z.2.2.2))), fun _ => rfl, fun _ => rfl⟩
  let realGroup : (Public × Real) × Test ≃ Real × Hybrid :=
    ⟨fun z => (z.1.2, ((fun j => (z.2.1 j, fun i => z.2.2.1 i j)),
      (z.1.1, ((fun j i => z.2.2.2.1 i j), z.2.2.2.2)))),
      fun z => ((z.2.2.1, z.1), ((fun j => (z.2.1 j).1),
        ((fun i j => (z.2.1 j).2 i), ((fun i j => z.2.2.2.1 j i), z.2.2.2.2)))),
      fun _ => rfl, fun _ => rfl⟩
  let idealGroup : (Public × Values) × Test ≃ Values × Ideal :=
    ⟨fun z => (z.1.2, ((fun j i => z.2.2.2.1 i j),
      (z.1.1, ((fun j => (z.2.1 j, fun i => z.2.2.1 i j)), z.2.2.2.2)))),
      fun z => ((z.2.2.1, z.1), ((fun j => (z.2.2.2.1 j).1),
        ((fun i j => (z.2.2.2.1 j).2 i), ((fun i j => z.2.1 j i), z.2.2.2.2)))),
      fun _ => rfl, fun _ => rfl⟩
  have hhybrid (t : ℕ) : acceptProb (columnHybrid P χ w t) D =
      uprob (fun z : Hybrid => event t z.2.1 z.1 z.2.2.1 z.2.2.2) := by
    rw [acceptProb_def]
    exact uprob_comp_equiv hybridGroup (fun z : Hybrid => event t z.2.1 z.1 z.2.2.1 z.2.2.2)
  have hreal : acceptProb (LWE.sample P χ) (columnTest P χ w k D) =
      uprob (fun z : Real × Hybrid => event (k.val + 1) z.2.2.1
        (Function.update z.2.1 k z.1) z.2.2.2.1 z.2.2.2.2) := by
    rw [acceptProb_def, ← uprob_comp_equiv realGroup]
    apply congrArg uprob
    funext z
    dsimp only [event, realGroup, Equiv.coe_fn_mk, Prod.fst, Prod.snd]
    rw [columnTest_eq, LWE.sample_fst, LWE.sample_snd, columnHybrid_eq]
    refine congrArg (fun c => D c z.2.2.2.2 = true) (Prod.ext rfl ?_)
    apply Matrix.ext
    intro i j
    dsimp only [Prod.fst, Prod.snd]
    by_cases hj : j = k
    · subst j
      simp only [Matrix.of_apply, Function.update_self, Nat.lt_succ_self, if_true]
    · have hv : j.val ≠ k.val := fun h => hj (Fin.ext h)
      have hlt : j.val < k.val + 1 ↔ j.val < k.val := by omega
      simp only [Matrix.of_apply, if_neg hj, Function.update_of_ne hj, hlt]
  have hideal : acceptProb (id : Public × Values → _) (columnTest P χ w k D) =
      uprob (fun z : Values × Ideal => event k.val z.2.2.1 z.2.2.2.1
        (Function.update z.2.1 k z.1) z.2.2.2.2) := by
    rw [acceptProb_def, ← uprob_comp_equiv idealGroup]
    apply congrArg uprob
    funext z
    dsimp only [event, idealGroup, Equiv.coe_fn_mk, Prod.fst, Prod.snd]
    rw [columnTest_eq, columnHybrid_eq]
    simp only [id_eq]
    refine congrArg (fun c => D c z.2.2.2.2 = true) (Prod.ext rfl ?_)
    apply Matrix.ext
    intro i j
    dsimp only [Prod.fst, Prod.snd]
    by_cases hj : j = k
    · subst j
      simp only [Matrix.of_apply, if_true, if_neg (Nat.lt_irrefl _), Function.update_self]
    · simp only [Matrix.of_apply, if_neg hj, Function.update_of_ne hj]
  simp only [LWE.decisionAdvantage_eq, distAdv_def, hhybrid, hreal, hideal]
  rw [OneWay.uprob_update k (fun cols (z : Public × ((Fin w → Values) × ρ)) =>
    event (k.val + 1) z.1 cols z.2.1 z.2.2),
    OneWay.uprob_update k (fun cols (z : Public × ((Fin w → Real) × ρ)) =>
      event k.val z.1 z.2.1 cols z.2.2)]
  rw [← uprob_comp_equiv swap (fun z : Ideal => event k.val z.2.1 z.2.2.1 z.1 z.2.2.2)]
  rfl

/-- Distinguishing a concealed matrix from uniform costs the sum of its standard
fixed-sample DLWE column advantages [PW10, Section 6.2].

**Proof sketch.** The zero hybrid is uniform after ignoring unused coins; hybrid `w`
is the actual concealed sampler by `conceal_column`. Telescope neighboring acceptance
differences and apply the real triangle inequality and `column_gap`. At `w=0` the
second matrix has one possible value and the sum of advantages is empty. -/
theorem concealed_advantage_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : Noise) (w : ℕ)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)) → ρ → Bool) :
    distAdv (concealedSampler P χ w)
      (id : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
        Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)) → _) D ≤
      ∑ k : Fin w, LWE.decisionAdvantage P χ (columnTest P χ w k D) := by
  classical
  let Public := Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus)
  let Secrets := Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus)
  let Errors := Fin P.samples → Fin w → χ.Coins
  let Uniform := Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)
  let Hybrid := Public × (Secrets × (Errors × Uniform))
  have hzero : acceptProb (columnHybrid P χ w 0) D = acceptProb (id : Public × Uniform → _) D := by
    let group : Hybrid × ρ ≃ ((Public × Uniform) × ρ) × (Secrets × Errors) :=
      ⟨fun z => (((z.1.1, z.1.2.2.2), z.2), (z.1.2.1, z.1.2.2.1)),
        fun z => ((z.1.1.1, (z.2.1, (z.2.2, z.1.1.2))), z.1.2),
        fun _ => rfl, fun _ => rfl⟩
    let test (z : (Public × Uniform) × ρ) := D (id z.1) z.2 = true
    rw [acceptProb_def, acceptProb_def, ← uprob_fst (β := Secrets × Errors) test,
      ← uprob_comp_equiv group (fun z => test z.1)]
    apply congrArg uprob
    funext z
    simp only [columnHybrid_eq, Nat.not_lt_zero, if_false, group, Equiv.coe_fn_mk, test, id_eq]
    rfl
  have hfull : acceptProb (columnHybrid P χ w w) D = acceptProb (concealedSampler P χ w) D := by
    let group : Hybrid × ρ ≃ ((Public × (Secrets × Errors)) × ρ) × Uniform :=
      ⟨fun z => (((z.1.1, (z.1.2.1, z.1.2.2.1)), z.2), z.1.2.2.2),
        fun z => ((z.1.1.1, (z.1.1.2.1, (z.1.1.2.2, z.2))), z.1.2),
        fun _ => rfl, fun _ => rfl⟩
    let test (z : (Public × (Secrets × Errors)) × ρ) := D (concealedSampler P χ w z.1) z.2 = true
    rw [acceptProb_def, acceptProb_def, ← uprob_fst (β := Uniform) test,
      ← uprob_comp_equiv group (fun z => test z.1)]
    apply congrArg uprob
    funext z
    dsimp only [test, group, Equiv.coe_fn_mk, Prod.fst, Prod.snd]
    rw [columnHybrid_eq, concealedSampler_eq]
    refine congrArg (fun key => D key z.2 = true) (Prod.ext rfl ?_)
    apply Matrix.ext
    intro i j
    simp only [Matrix.of_apply, if_pos j.isLt, conceal_column]
  let score (t : ℕ) := acceptProb (columnHybrid P χ w t) D
  rw [distAdv_def, ← hfull, ← hzero, abs_sub_comm]
  change |score 0 - score w| ≤ _
  calc
    _ ≤ ∑ i ∈ Finset.range w, |score i - score (i + 1)| := abs_sub_le_sum_hybrids score w
    _ = _ := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [abs_sub_comm]
      exact column_gap P χ w k D

/-- Add a fixed public matrix to the concealed block, covering gadget key modes
and fixed all-but-one branches [PW10, Sections 6.2--6.4]. -/
@[simps! (config := { isSimp := false }) fst snd]
def shiftedSampler (P : Parameters) (χ : Noise) (w : ℕ)
    (M : Matrix (Fin P.samples) (Fin w) (ZMod P.modulus))
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → Fin w → χ.Coins))) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      Matrix (Fin P.samples) (Fin w) (ZMod P.modulus) :=
  ((concealedSampler P χ w r).1, (concealedSampler P χ w r).2 + M)

/-- The complete shifted sampler adds the specified public matrix only to its second block. -/
theorem shiftedSampler_eq (P : Parameters) (χ : Noise) (w : ℕ)
    (M : Matrix (Fin P.samples) (Fin w) (ZMod P.modulus))
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Matrix (Fin w) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → Fin w → χ.Coins))) :
    shiftedSampler P χ w M r =
      ((concealedSampler P χ w r).1, (concealedSampler P χ w r).2 + M) := rfl

/-- Two fixed public shifts of concealed keys cost two sums of standard DLWE
advantages [PW10, Sections 6.2--6.4, explicit two-mode bound].

**Proof sketch.** For each shift, compose it into the distinguisher and apply
`concealed_advantage_le`. Adding the fixed matrix is a bijection, so both ideal
distributions are the same full uniform matrix pair. Insert that common ideal
experiment and apply the absolute-value triangle inequality. -/
theorem shifted_advantage_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : Noise) (w : ℕ)
    (M₀ M₁ : Matrix (Fin P.samples) (Fin w) (ZMod P.modulus))
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)) → ρ → Bool) :
    distAdv (shiftedSampler P χ w M₀) (shiftedSampler P χ w M₁) D ≤
      (∑ k : Fin w, LWE.decisionAdvantage P χ
        (columnTest P χ w k (fun c r => D (c.1, c.2 + M₀) r))) +
      ∑ k : Fin w, LWE.decisionAdvantage P χ
        (columnTest P χ w k (fun c r => D (c.1, c.2 + M₁) r)) := by
  let Public := Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus)
  let Block := Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)
  let Key := Public × Block
  let Dshift (M : Block) (c : Key) (r : ρ) := D (c.1, c.2 + M) r
  let ideal : Key → Key := id
  have hbound (M : Block) : distAdv (shiftedSampler P χ w M) ideal D ≤
      ∑ k : Fin w, LWE.decisionAdvantage P χ (columnTest P χ w k (Dshift M)) := by
    have hreal : acceptProb (shiftedSampler P χ w M) D =
        acceptProb (concealedSampler P χ w) (Dshift M) := by
      simp only [acceptProb_def, shiftedSampler_eq, Dshift]
    have huniform : acceptProb ideal D = acceptProb ideal (Dshift M) := by
      let move : Key ≃ Key := (Equiv.refl Public).prodCongr (Equiv.addRight M)
      rw [acceptProb_def, acceptProb_def]
      exact (uprob_comp_equiv (move.prodCongr (Equiv.refl ρ))
        (fun z : Key × ρ => D z.1 z.2 = true)).symm
    rw [distAdv_def, hreal, huniform, ← distAdv_def]
    exact concealed_advantage_le P χ w (Dshift M)
  have htriangle : distAdv (shiftedSampler P χ w M₀) (shiftedSampler P χ w M₁) D ≤
      distAdv (shiftedSampler P χ w M₀) ideal D + distAdv (shiftedSampler P χ w M₁) ideal D := by
    simp only [distAdv_def]
    calc
      _ ≤ |acceptProb (shiftedSampler P χ w M₀) D - acceptProb ideal D| +
          |acceptProb ideal D - acceptProb (shiftedSampler P χ w M₁) D| := abs_sub_le _ _ _
      _ = _ := by rw [abs_sub_comm (acceptProb ideal D)]
  exact htriangle.trans (add_le_add (hbound M₀) (hbound M₁))

end TCSlib.Cryptography.TrapdoorFunctions.Lossy
