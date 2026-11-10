/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Matrix
import TCSlib.Cryptography.LWE.Experiments

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
for its columns. Two fixed public shifts cost two such sums. All claims are concrete
statement-phase admissions; efficient asymptotic key-generation bridges remain separate.

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
  sorry

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

**Proof sketch.** Reassociate independent seeds. In the real challenge, exchange the
challenge secret/noise with the otherwise unused seed of column `k`; the challenge
matrix remains the same common matrix for every column. The uniform challenge
supplies exactly the next independent uniform column. Unused coins do not change tests. -/
theorem column_gap {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : Noise) (w : ℕ) (k : Fin w)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      Matrix (Fin P.samples) (Fin w) (ZMod P.modulus)) → ρ → Bool) :
    distAdv (columnHybrid P χ w (k.val + 1)) (columnHybrid P χ w k.val) D =
      LWE.decisionAdvantage P χ (columnTest P χ w k D) := by
  sorry

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
  sorry

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
  sorry

end TCSlib.Cryptography.TrapdoorFunctions.Lossy
