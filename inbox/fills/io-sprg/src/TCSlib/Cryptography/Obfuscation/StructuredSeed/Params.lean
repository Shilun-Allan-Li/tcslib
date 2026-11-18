/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs
import TCSlib.Cryptography.Obfuscation.StructuredSeed.LPN
import TCSlib.Cryptography.Asymptotic.UniversalPadding.Parameter
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Rational parameters and dimensions of the JLS construction

## Main definitions

* `Params`: rational noise exponent, fixed degree/schedule, and efficient Boolean PRG.
* Rounded dimensions, inverse parameter maps, and explicit public/private coordinates.
* `Params.lpnFamily_raw`: the construction's dimension-indexed exact LPN family.

## Main results

* Inverse-schedule identities and eventual parameter side conditions.
* Every algorithm takes a public prime; Params contains no prime schedule.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity

/-- The construction fixes degree, rational noise exponent, polynomial schedule
exponent, and an efficient Boolean PRG [JLS26, Theorem 4.1, p. 11; §4, p. 15].
Dv9: no prime is stored. SP-W1: δ is rational data, per the user's ruling,
so the exact rounded noise schedule can have a uniform implementation.
Dv11 requires positive degree, and Dv4 carries the multilinear representation. -/
structure Params where
  d : ℕ
  one_le_d : 1 ≤ d
  δ : ℚ
  δ_pos : 0 < δ
  δ_lt_one : δ < 1
  E : ℕ
  one_le_E : 1 ≤ E
  G : BoolPRG
  R : G.MultilinearRep d

namespace Params

/-- Half-degree is `D = (d+1)/2` [JLS26, §4, p. 15]. Dv11 ensures D>0. -/
def D (P : Params) : ℕ := (P.d + 1) / 2

/-- Half-degree equals (d+1)/2; glue. -/
theorem D_eq (P : Params) : P.D = (P.d + 1) / 2 := rfl

/-- LPN dimension is `ℓ(κ)=κ^E` [JLS26, §4, p. 15]. Dv1 fixes a polynomial schedule. -/
def ℓ (P : Params) (κ : ℕ) : ℕ := κ ^ P.E

/-- The LPN dimension equals κ^E; glue. -/
theorem ℓ_eq (P : Params) (κ : ℕ) : P.ℓ κ = κ ^ P.E := rfl

/-- Boolean seed length is `n=ℓ^D` [JLS26, §4, p. 15]. Dv1 makes this an exact power. -/
def n (P : Params) (κ : ℕ) : ℕ := P.ℓ κ ^ P.D

/-- The Boolean seed length is ℓ^D; glue. -/
theorem n_eq (P : Params) (κ : ℕ) : P.n κ = P.ℓ κ ^ P.D := rfl

/-- Output length is the underlying generator's `m=G.outLen(n)`
[JLS26, §4, p. 15]. Dv5 uses a stretch lower bound rather than exact equality. -/
def m (P : Params) (κ : ℕ) : ℕ := P.G.outLen (P.n κ)

/-- Output length reads the generator's schedule; glue. -/
theorem m_eq (P : Params) (κ : ℕ) : P.m κ = P.G.outLen (P.n κ) := rfl

/-- The rounded square-root noise denominator is max 1 floor(L^(δ/2))
[JLS26, §4, p. 15]. Dv3 rounds in the noisier direction; SP-W1 uses rational δ. -/
noncomputable def noiseWidth (P : Params) (L : ℕ) : ℕ :=
  max 1 ⌊(L : ℝ) ^ ((P.δ : ℝ) / 2)⌋₊

/-- The rounded noise width is the stated real-power floor; glue. -/
theorem noiseWidth_eq (P : Params) (L : ℕ) :
    P.noiseWidth L = max 1 ⌊(L : ℝ) ^ ((P.δ : ℝ) / 2)⌋₊ := rfl

/-- The exact LPN denominator at dimension L is noiseWidth(L)^2
[JLS26, Definition 2.3, pp. 9-10]. Dv3 uses the rounded rational rate 1/W. -/
noncomputable def noiseDenAt (P : Params) (L : ℕ) : ℕ := P.noiseWidth L ^ 2

/-- The noise denominator is the square of noiseWidth; glue. -/
theorem noiseDenAt_eq (P : Params) (L : ℕ) : P.noiseDenAt L = P.noiseWidth L ^ 2 := rfl

/-- At κ, `w=noiseWidth(ℓ κ)` [JLS26, §4, p. 15]. Dv3 and SP-W1 fix rounding. -/
noncomputable def w (P : Params) (κ : ℕ) : ℕ := P.noiseWidth (P.ℓ κ)

/-- The construction's noise width is indexed by ℓ; glue. -/
theorem w_eq (P : Params) (κ : ℕ) : P.w κ = P.noiseWidth (P.ℓ κ) := rfl

/-- The noise denominator is `W=w^2` [JLS26, §4, p. 15]. Dv3 rounds the rate to 1/W. -/
noncomputable def W (P : Params) (κ : ℕ) : ℕ := P.w κ ^ 2

/-- W is the square of w; glue. -/
theorem W_eq (P : Params) (κ : ℕ) : P.W κ = P.w κ ^ 2 := rfl

/-- The two descriptions of W agree at ℓ(κ); glue. -/
theorem W_eq_noiseDenAt (P : Params) (κ : ℕ) : P.W κ = P.noiseDenAt (P.ℓ κ) := rfl

/-- Slack is `t=κ` [JLS26, §4, p. 15]. -/
def t (_P : Params) (κ : ℕ) : ℕ := κ

/-- Slack equals κ; glue. -/
theorem t_eq (P : Params) (κ : ℕ) : P.t κ = κ := rfl

/-- Grid side is `rc=t*w` [JLS26, §4, p. 15]. Dv3 makes capacity an exact square. -/
noncomputable def rc (P : Params) (κ : ℕ) : ℕ := P.t κ * P.w κ

/-- The grid side is t*w; glue. -/
theorem rc_eq (P : Params) (κ : ℕ) : P.rc κ = P.t κ * P.w κ := rfl

/-- Bucket capacity is `cap=rc^2` [JLS26, §4, p. 15]. Dv3 fixes integral rounding. -/
noncomputable def cap (P : Params) (κ : ℕ) : ℕ := P.rc κ ^ 2

/-- Capacity is the squared grid side; glue. -/
theorem cap_eq (P : Params) (κ : ℕ) : P.cap κ = P.rc κ ^ 2 := rfl

/-- Bucket count is max 1 ceil(m*t/W) [JLS26, §4, p. 15]. Dv3 keeps the draw inhabited. -/
noncomputable def B (P : Params) (κ : ℕ) : ℕ :=
  max 1 ((P.m κ * P.t κ + P.W κ - 1) / P.W κ)

/-- Bucket count is the positive rounded quotient; glue. -/
theorem B_eq (P : Params) (κ : ℕ) :
    P.B κ = max 1 ((P.m κ * P.t κ + P.W κ - 1) / P.W κ) := rfl

/-- Bad-output threshold is floor(m*log₂(n)/W) [JLS26, §4, p. 15]. Dv3 fixes the floor. -/
noncomputable def Γ (P : Params) (κ : ℕ) : ℕ :=
  P.m κ * Nat.log 2 (P.n κ) / P.W κ

/-- The bad-output threshold is the integer quotient; glue. -/
theorem Γ_eq (P : Params) (κ : ℕ) :
    P.Γ κ = P.m κ * Nat.log 2 (P.n κ) / P.W κ := rfl

/-- The inverse LPN schedule is the greatest κ with κ^E≤L [JLS26, Remark 2.1, p. 9].
Dv1 and Dv3 reindex the fixed LPN family by its own secret dimension. -/
def kappaOf (P : Params) (L : ℕ) : ℕ :=
  Nat.findGreatest (fun κ => κ ^ P.E ≤ L) L

/-- The LPN inverse is a bounded greatest search; glue. -/
theorem kappaOf_eq (P : Params) (L : ℕ) :
    P.kappaOf L = Nat.findGreatest (fun κ => κ ^ P.E ≤ L) L := rfl

/-- The inverse Boolean schedule uses exponent E*D [JLS26, Remark 2.1, p. 9].
Dv1 reindexes the Boolean assumption by its seed length. -/
def kappaOfN (P : Params) (N : ℕ) : ℕ :=
  Nat.findGreatest (fun κ => κ ^ (P.E * P.D) ≤ N) N

/-- The Boolean inverse is a bounded greatest search; glue. -/
theorem kappaOfN_eq (P : Params) (N : ℕ) :
    P.kappaOfN N = Nat.findGreatest (fun κ => κ ^ (P.E * P.D) ≤ N) N := rfl

/-- The public seed contains κ blocks of n residues and one error flag
[JLS26, SdSamp', pp. 15-16]. Dv2 counts field elements before their bit widths. -/
def pubLen (P : Params) (κ : ℕ) : ℕ := κ * P.n κ + 1

/-- Public length is κ*n+1; glue. -/
theorem pubLen_eq (P : Params) (κ : ℕ) : P.pubLen κ = κ * P.n κ + 1 := rfl

/-- One instance's private coordinates are tensor, U and V positions
[JLS26, Equation (2), p. 16]. Dv15 retains explicit finite coordinate types. -/
abbrev SVar (P : Params) (κ : ℕ) : Type :=
  (Fin P.D → Fin (P.ℓ κ + 1)) ⊕
    (Fin (P.B κ) × ((Fin (P.rc κ) × Fin (P.t κ)) ⊕ (Fin (P.t κ) × Fin (P.rc κ))))

/-- The private-coordinate type is the tensor/factor sum; glue. -/
theorem SVar_eq (P : Params) (κ : ℕ) : P.SVar κ =
    ((Fin P.D → Fin (P.ℓ κ + 1)) ⊕
      (Fin (P.B κ) × ((Fin (P.rc κ) × Fin (P.t κ)) ⊕
        (Fin (P.t κ) × Fin (P.rc κ))))) := rfl

/-- One private instance has (ℓ+1)^D+ B*(rc*t+t*rc) coordinates
[JLS26, Equation (2), p. 16]. Dv2 uses integral dimensions. -/
noncomputable def sLen (P : Params) (κ : ℕ) : ℕ :=
  (P.ℓ κ + 1) ^ P.D + P.B κ * (P.rc κ * P.t κ + P.t κ * P.rc κ)

/-- The instance-private length is the explicit dimension formula; glue. -/
theorem sLen_eq (P : Params) (κ : ℕ) : P.sLen κ =
    (P.ℓ κ + 1) ^ P.D + P.B κ * (P.rc κ * P.t κ + P.t κ * P.rc κ) := rfl

/-- Structured private variables are κ copies of flag, S and flag*S
[JLS26, SdSamp', p. 16]. Dv15 transports these coordinates explicitly to Fin. -/
abbrev Priv (P : Params) (κ : ℕ) : Type :=
  Fin κ × (Unit ⊕ (P.SVar κ ⊕ P.SVar κ))

/-- The structured-private type has three components per repetition; glue. -/
theorem priv_eq (P : Params) (κ : ℕ) :
    P.Priv κ = (Fin κ × (Unit ⊕ (P.SVar κ ⊕ P.SVar κ))) := rfl

/-- Private length is κ*(1+2*sLen) [JLS26, SdSamp', p. 16]. Dv2 counts residues. -/
noncomputable def privLen (P : Params) (κ : ℕ) : ℕ := κ * (1 + (P.sLen κ + P.sLen κ))

/-- Private length is the explicit flag/two-copy formula; glue. -/
theorem privLen_eq (P : Params) (κ : ℕ) :
    P.privLen κ = κ * (1 + (P.sLen κ + P.sLen κ)) := rfl

/-- The tensor/factor coordinate enumeration is explicit [JLS26, Equation (2), p. 16].
Dv15 uses only the published Fin sum, product and function equivalences. -/
noncomputable def sVarEquiv (P : Params) (κ : ℕ) : P.SVar κ ≃ Fin (P.sLen κ) :=
  (Equiv.sumCongr finFunctionFinEquiv
    ((Equiv.prodCongr (Equiv.refl _)
      ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)).trans
        finProdFinEquiv)).trans finSumFinEquiv

/-- The private-coordinate enumeration is its stated composition; glue. -/
theorem sVarEquiv_eq (P : Params) (κ : ℕ) : P.sVarEquiv κ =
    (Equiv.sumCongr finFunctionFinEquiv
      ((Equiv.prodCongr (Equiv.refl _)
        ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)).trans
          finProdFinEquiv)).trans finSumFinEquiv := rfl

/-- The complete private-variable enumeration uses the same explicit equivalences
[JLS26, SdSamp', p. 16]. Dv15 adds no classical enumeration. -/
noncomputable def privEquiv (P : Params) (κ : ℕ) : P.Priv κ ≃ Fin (P.privLen κ) :=
  (Equiv.prodCongr (Equiv.refl _)
    ((Equiv.sumCongr finOneEquiv.symm
      ((Equiv.sumCongr (P.sVarEquiv κ) (P.sVarEquiv κ)).trans finSumFinEquiv)).trans
        finSumFinEquiv)).trans finProdFinEquiv

/-- The complete-private enumeration is its stated composition; glue. -/
theorem privEquiv_eq (P : Params) (κ : ℕ) : P.privEquiv κ =
    (Equiv.prodCongr (Equiv.refl _)
      ((Equiv.sumCongr finOneEquiv.symm
        ((Equiv.sumCongr (P.sVarEquiv κ) (P.sVarEquiv κ)).trans finSumFinEquiv)).trans
          finSumFinEquiv)).trans finProdFinEquiv := rfl

/-- Structured public variables are the repeated n-vectors and the error flag
[JLS26, SdSamp', p. 16]. Dv15 provides a fixed coordinate enumeration. -/
abbrev Pub (P : Params) (κ : ℕ) : Type := (Fin κ × Fin (P.n κ)) ⊕ Unit

/-- The structured public type is a vector-block sum with one flag; glue. -/
theorem pub_eq (P : Params) (κ : ℕ) :
    P.Pub κ = ((Fin κ × Fin (P.n κ)) ⊕ Unit) := rfl

/-- The public-variable enumeration splits repeated blocks from the flag
[JLS26, SdSamp', p. 16]. Dv15 uses explicit Fin equivalences. -/
def pubEquiv (P : Params) (κ : ℕ) : P.Pub κ ≃ Fin (P.pubLen κ) :=
  (Equiv.sumCongr finProdFinEquiv finOneEquiv.symm).trans finSumFinEquiv

/-- The public enumeration is its explicit sum/product composition; glue. -/
theorem pubEquiv_eq (P : Params) (κ : ℕ) : P.pubEquiv κ =
    (Equiv.sumCongr finProdFinEquiv finOneEquiv.symm).trans finSumFinEquiv := rfl

/-- The construction index contains I, bucket placement and the LPN matrix
[JLS26, IdSamp', p. 15]. Dv3 transposes A, and Dv15 derives grid positions. -/
abbrev Idx' (P : Params) (κ : ℕ) (pp : PrimeParam κ) : Type :=
  P.G.Idx (P.n κ) × ((Fin (P.m κ) → Fin (P.B κ)) ×
    Matrix (Fin (P.n κ)) (Fin (P.ℓ κ)) (ZMod pp.p))

/-- The construction index is the stated triple; glue. -/
theorem idx'_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) : P.Idx' κ pp =
    (P.G.Idx (P.n κ) × ((Fin (P.m κ) → Fin (P.B κ)) ×
      Matrix (Fin (P.n κ)) (Fin (P.ℓ κ)) (ZMod pp.p))) := rfl

/-- Half-degree is positive [JLS26, §4, p. 15]. Dv11 assumes d≥1.

**Proof sketch.** Divide the inequality d+1≥2 by two. -/
theorem D_pos (P : Params) : 0 < P.D := by
  rw [P.D_eq]
  exact Nat.div_pos_iff.mpr
    ⟨Nat.succ_pos 1, Nat.succ_le_succ P.one_le_d⟩

/-- Noise width is positive at every dimension [JLS26, §4, p. 15]. Dv3 uses max 1.

**Proof sketch.** The maximum dominates one. -/
theorem noiseWidth_pos (P : Params) (L : ℕ) : 0 < P.noiseWidth L := by
  rw [P.noiseWidth_eq]
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

/-- The scalar denominator is positive [JLS26, §4, p. 15]. Dv3 squares a positive width.

**Proof sketch.** Use noiseWidth positivity and positivity of its square. -/
theorem noiseDenAt_pos (P : Params) (L : ℕ) : 0 < P.noiseDenAt L := by
  rw [P.noiseDenAt_eq]
  exact pow_pos (P.noiseWidth_pos L) 2

/-- W is positive at every κ [JLS26, §4, p. 15]. Dv3 keeps noise seeds nonempty.

**Proof sketch.** Use the width lower bound and the square formula. -/
theorem W_pos (P : Params) (κ : ℕ) : 0 < P.W κ := by
  rw [P.W_eq_noiseDenAt]
  exact P.noiseDenAt_pos _

/-- Bucket count is positive at every κ [JLS26, §4, p. 15]. Dv3 uses max 1.

**Proof sketch.** The maximum dominates one. -/
theorem B_pos (P : Params) (κ : ℕ) : 0 < P.B κ := by
  rw [P.B_eq]
  exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

instance instWNeZero (P : Params) (κ : ℕ) : NeZero (P.W κ) := ⟨Nat.ne_of_gt (P.W_pos κ)⟩
instance instBNeZero (P : Params) (κ : ℕ) : NeZero (P.B κ) := ⟨Nat.ne_of_gt (P.B_pos κ)⟩

/-- The LPN inverse returns κ on κ^E [JLS26, Remark 2.1, p. 9]. Dv1 uses exact powers.

**Proof sketch.** Strict monotonicity of positive natural powers characterizes the greatest
candidate in the bounded search. -/
theorem kappaOf_pow (P : Params) (κ : ℕ) : P.kappaOf (P.ℓ κ) = κ := by
  simp only [P.kappaOf_eq, P.ℓ_eq, ← PadQuad.nu_eq]
  apply le_antisymm
  · exact (Nat.pow_le_pow_iff_left (Nat.one_le_iff_ne_zero.mp P.one_le_E)).1
      (PadQuad.nu_pow_le P.one_le_E (κ ^ P.E))
  · exact PadQuad.le_nu P.one_le_E le_rfl

/-- The inverse LPN parameter never exceeds its input [JLS26, Remark 2.1, p. 9].

**Proof sketch.** Apply the bounded-greatest-search upper bound. -/
theorem kappaOf_le (P : Params) (L : ℕ) : P.kappaOf L ≤ L := by
  simpa only [P.kappaOf_eq, PadQuad.nu_eq] using PadQuad.nu_le P.E L

/-- The Boolean inverse returns κ on n(κ) [JLS26, Remark 2.1, p. 9]. Dv1 uses exact powers.

**Proof sketch.** Rewrite n as κ^(E*D), then apply strict monotonicity of positive powers. -/
theorem kappaOfN_n (P : Params) (κ : ℕ) : P.kappaOfN (P.n κ) = κ := by
  have hED : 1 ≤ P.E * P.D :=
    Nat.mul_le_mul P.one_le_E (Nat.succ_le_of_lt P.D_pos)
  simp only [P.kappaOfN_eq, P.n_eq, P.ℓ_eq, ← Nat.pow_mul, ← PadQuad.nu_eq]
  apply le_antisymm
  · exact (Nat.pow_le_pow_iff_left (Nat.one_le_iff_ne_zero.mp hED)).1
      (PadQuad.nu_pow_le hED (κ ^ (P.E * P.D)))
  · exact PadQuad.le_nu hED le_rfl

/-- The inverse Boolean parameter never exceeds its input [JLS26, Remark 2.1, p. 9].

**Proof sketch.** Apply the bounded-greatest-search upper bound. -/
theorem kappaOfN_le (P : Params) (N : ℕ) : P.kappaOfN N ≤ N := by
  simpa only [P.kappaOfN_eq, PadQuad.nu_eq] using PadQuad.nu_le (P.E * P.D) N

/-- The prime chosen at inverse dimension L fits L+1 residue bits
[JLS26, Definition 2.3, pp. 9-10]. Dv3 uses the family's own input dimension.

**Proof sketch.** The schedule's width bound and kappaOf_le give the result. -/
theorem lpnModulus_le_pow (P : Params) (π : PrimeSchedule) (L : ℕ) :
    (π (P.kappaOf L)).p ≤ 2 ^ (L + 1) :=
  (π (P.kappaOf L)).le_two_pow.trans
  (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.add_le_add_right (P.kappaOf_le L) 1))

/-- The sample count L^D is bounded by its syntactic polynomial; glue.

**Proof sketch.** Read the power and variable equations of PolyExpr. -/
theorem lpnSamples_le (P : Params) (L : ℕ) :
    L ^ P.D ≤ (PolyExpr.pow .var P.D).eval L := by
  rw [PolyExpr.eval_pow, PolyExpr.eval_var]

/-- The construction's raw LPN family is indexed by its own secret dimension
[JLS26, Definition 2.3, pp. 9-10]. Dv3 fixes its sample schedule, transpose,
rounded noise and L+1-bit residues. Dv9 reads an arbitrary public prime schedule.
SP-W1 uses rational δ; sampler efficiency is added only in the target assembly. -/
noncomputable def lpnFamily_raw (P : Params) (π : PrimeSchedule) : LPNFamily.Raw where
  samples L := L ^ P.D
  modulus L := (π (P.kappaOf L)).p
  noiseDen := P.noiseDenAt
  modulus_prime L := (π (P.kappaOf L)).prime
  noiseDen_pos := P.noiseDenAt_pos
  samplesBound := .pow .var P.D
  residueBits := .add .var (.const 1)
  samples_le := P.lpnSamples_le
  modulus_le_pow L := by
    simpa only [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const] using
      P.lpnModulus_le_pow π L

/-- The LPN family's sample schedule is L^D; glue. -/
theorem lpnFamily_raw_samples (P : Params) (π : PrimeSchedule) (L : ℕ) :
    (P.lpnFamily_raw π).samples L = L ^ P.D := rfl

/-- The LPN modulus comes from the inverse-indexed schedule; glue. -/
theorem lpnFamily_raw_modulus (P : Params) (π : PrimeSchedule) (L : ℕ) :
    (P.lpnFamily_raw π).modulus L = (π (P.kappaOf L)).p := rfl

/-- The LPN noise denominator is the dimension-indexed rounded square; glue. -/
theorem lpnFamily_raw_noiseDen (P : Params) (π : PrimeSchedule) (L : ℕ) :
    (P.lpnFamily_raw π).noiseDen L = P.noiseDenAt L := rfl

/-- The LPN sample bound is the power expression; glue. -/
theorem lpnFamily_raw_samplesBound (P : Params) (π : PrimeSchedule) :
    (P.lpnFamily_raw π).samplesBound = .pow .var P.D := rfl

/-- The LPN residue width is the identity plus one; glue. -/
theorem lpnFamily_raw_residueBits (P : Params) (π : PrimeSchedule) :
    (P.lpnFamily_raw π).residueBits = .add .var (.const 1) := rfl

/-- The Boolean seed length dominates κ [JLS26, Remark 2.1, p. 9]. Dv1 uses E,D≥1.

**Proof sketch.** Natural powers with positive exponents dominate their bases. -/
theorem le_n (P : Params) (κ : ℕ) : κ ≤ P.n κ := by
  rw [P.n_eq, P.ℓ_eq]
  exact (Nat.le_pow (lt_of_lt_of_le Nat.zero_lt_one P.one_le_E)).trans
    (Nat.le_pow P.D_pos)

/-- Eventually Γ≤B [JLS26, Claim 4.2, pp. 19-21]. Dv7 makes the threshold explicit.

**Proof sketch.** The logarithm of a fixed polynomial is eventually below κ; compare the
rounded quotients using W>0. -/
theorem Γ_le_B (P : Params) : ∃ κ₀, ∀ κ ≥ κ₀, P.Γ κ ≤ P.B κ := by
  have hsmall : Asymptotics.IsLittleO Filter.atTop
      (fun κ : ℕ => ((P.D : ℝ) * (P.E : ℝ)) * Real.logb 2 (κ : ℝ))
      (fun κ : ℕ => (κ : ℝ)) :=
    ((Real.isLittleO_logb_id_atTop (b := 2)).const_mul_left
      ((P.D : ℝ) * (P.E : ℝ))).comp_tendsto tendsto_natCast_atTop_atTop
  obtain ⟨κ₀, hκ₀⟩ := Filter.eventually_atTop.mp hsmall.eventuallyLE
  refine ⟨κ₀, ?_⟩
  intro κ hκ
  have hnorm := hκ₀ κ hκ
  change ‖((P.D : ℝ) * (P.E : ℝ)) * Real.logb 2 (κ : ℝ)‖ ≤ ‖(κ : ℝ)‖ at hnorm
  simp only [Real.norm_eq_abs, Nat.abs_cast] at hnorm
  have hlogn : Real.logb 2 (P.n κ : ℝ) =
      ((P.D : ℝ) * (P.E : ℝ)) * Real.logb 2 (κ : ℝ) := ?_
  swap
  · rw [P.n_eq, P.ℓ_eq, Nat.cast_pow, Nat.cast_pow, Real.logb_pow,
      Real.logb_pow, mul_assoc]
  have hlog : Nat.log 2 (P.n κ) ≤ κ := ?_
  swap
  · have hcast : (Nat.log 2 (P.n κ) : ℝ) ≤ (κ : ℝ) :=
      (Real.natLog_le_logb (P.n κ) 2).trans
        (hlogn.le.trans ((le_abs_self _).trans hnorm))
    exact_mod_cast hcast
  have hround : P.m κ * κ ≤ P.m κ * κ + P.W κ - 1 := ?_
  swap
  · have hW := P.W_pos κ
    omega
  rw [P.Γ_eq, P.B_eq, P.t_eq]
  exact (Nat.div_le_div_right (Nat.mul_le_mul_left _ hlog)).trans
    ((Nat.div_le_div_right hround).trans (le_max_right _ _))

/-- The logarithm of n eventually exceeds every constant [JLS26, Claim 4.2, p. 20].
Dv7 uses an eventual threshold.

**Proof sketch.** The positive power schedule tends to infinity and Nat.log is unbounded. -/
theorem le_log_n (P : Params) (c : ℕ) :
    ∃ κ₀, ∀ κ ≥ κ₀, c ≤ Nat.log 2 (P.n κ) := by
  refine ⟨2 ^ c, ?_⟩
  intro κ hκ
  exact Nat.le_log_of_pow_le Nat.one_lt_two (hκ.trans (P.le_n κ))


end Params
end TCSlib.Cryptography.Obfuscation.StructuredSeed
