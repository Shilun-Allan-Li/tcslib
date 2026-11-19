import Lean
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
import TCSlib.Cryptography.LWE.Ratio
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bootstrapped GSW at a polynomial modulus-to-noise ratio

## Main definitions

* `Parameters.ofFamily F κ`: the GSW parameters of an LWE family at `κ`, gadget width the
  family's residue width.
* `pBoot F`: an explicit syntactic polynomial in `κ` built from the family's dimension, sample
  and residue-width bounds.

## Main results

* `Parameters.ofFamily_columns_le`: `N ≤ (d(κ) + 1)·ℓ(κ)` at `ofFamily F κ` (glue, shared by
  G16 and the asymptotic forms of `GSW/Asymptotic.lean`).
* `bootRatio_le_poly` (G16): `8·(ℓ·bootNoise (ofFamily F κ) (m·B κ)) ≤ pBoot(κ)·B(κ)`.
* `decrypt_fheEval_of_ratio`, `decrypt_leveledEval_of_ratio` (G17, split into the pure and the
  leveled scheme): if `pBoot(κ)·B(κ) < q(κ)` and the noise is `B(κ)`-bounded, bootstrapped
  GSW at `κ` is correct on every circuit, pure (G12) and leveled (L3).

All three are proved here. With `LWE.Family.RatioBounded F B p` the
condition `pBoot(κ)·B(κ) < q(κ)` is the regime of a polynomial ratio `q/B` (assumption (A2)).

**Sources and reconstruction (P6-Q19 B), for the leveled statement.** The key chain is
Gentry's [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003], with his reverse order of
the levels undone (`GSW/Leveled.lean`); his correctness theorem for the leveled scheme is
[Gen09, Thm 4.2.1, p. 49, p059-b001] (only its statement is ingested). The hybrid order,
[Gen09, Thm 4.2.3, pp. 50–51, p060-b001, p061-b001], concerns security and is used in
`GSW/LeveledSecurity.lean`, not here.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: §3.4, Thm 3.7.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Thm 3.1, Def 3.6.
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
  8 June 2013: §3.1 (parameters).
* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
  September 2009: §4.1, Thm 4.2.1, Thm 4.2.3.

**Deviations.** Worst case, with an explicit polynomial (constant `2^70`; r3 §H6 drafted
`c < 2^70` with the factor `4`), not [BV14, Thm 3.7]'s `Θ̃` noise rate. The constant `8`
(r3 G16 wrote `4`) absorbs the floor in the decryption condition `2·(ℓ·β) < ⌊q/2⌋`, so that
`pBoot(κ)·B(κ) < q(κ)` suffices in G17.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Complexity
open Encryption.PublicKey

/-- **The GSW parameters of an LWE family** at the security parameter `κ` [GSW13, §3.1,
p008-b002; phase-5 §G4]: the family's LWE parameters, gadget width `ℓ = F.residueBits(κ)`, and
`q ≤ 2^ℓ` from the family's width bound, `(ofFamily F κ).lwe = F.parameters κ`,
`(ofFamily F κ).width = F.residueBits.eval κ`. Read only through its non-simp `simps` readers
`Parameters.ofFamily_lwe` and `Parameters.ofFamily_width` (type-level Rule 10). -/
@[simps (config := { isSimp := false }) lwe width]
def Parameters.ofFamily (F : LWE.Family) (κ : ℕ) : Parameters where
  lwe := F.parameters κ
  width := F.residueBits.eval κ
  modulus_le := F.modulus_le_pow κ

/-- **The bootstrapping polynomial** of a family (r3 G16 *(fix)*, settled here), with
`d = F.dimensionBound`, `s = F.samplesBound`, `r = F.residueBits`:
`pBoot F = 2^70 · r · ((d + 1)·r)^19 · (r + (d + 1)·r + 3)^4 · s`, evaluating to
`2^70·ℓ·N̂^19·(ℓ + N̂ + 3)^4·m̂` with `N̂ = (d(κ) + 1)·ℓ ≥ N` and `m̂ = s(κ) ≥ m` [BV14, Thm 3.7,
p016-b001, worst-case analogue]. Derivation: `bootNoise_le` (G13) gives
`bootNoise P β ≤ 4^33·N^19·X^4·(2β)` with `X = ℓ + ⌈log₂ N⌉ + 3 ≤ ℓ + N̂ + 3`; times `8·ℓ` and
with `β = m·B`, the constant is `8·4^33·2 = 2^70`. -/
def pBoot (F : LWE.Family) : PolyExpr :=
  .mul (.mul (.mul (.mul (.const (2 ^ 70)) F.residueBits)
      (.pow (.mul (.add F.dimensionBound (.const 1)) F.residueBits) 19))
    (.pow (.add (.add F.residueBits (.mul (.add F.dimensionBound (.const 1)) F.residueBits))
      (.const 3)) 4))
    F.samplesBound

/-- `pBoot F` is the expression `2^70 · r · ((d + 1)·r)^19 · (r + (d + 1)·r + 3)^4 · s` with
`d = F.dimensionBound`, `s = F.samplesBound`, `r = F.residueBits`. -/
theorem pBoot_eq (F : LWE.Family) :
    pBoot F =
      .mul (.mul (.mul (.mul (.const (2 ^ 70)) F.residueBits)
          (.pow (.mul (.add F.dimensionBound (.const 1)) F.residueBits) 19))
        (.pow (.add (.add F.residueBits (.mul (.add F.dimensionBound (.const 1)) F.residueBits))
          (.const 3)) 4))
        F.samplesBound := rfl

/-- **The ciphertext width of a family's parameters is polynomially bounded.** For every family
`F` and `κ`, `N = (n + 1)·ℓ` at `ofFamily F κ` is at most `(d(κ) + 1)·ℓ(κ)` with
`d = F.dimensionBound`, `ℓ(κ) = F.residueBits.eval κ`,
`(Parameters.ofFamily F κ).columns ≤ (F.dimensionBound.eval κ + 1) * F.residueBits.eval κ`.
Glue: `Parameters.columns_eq` read through `Parameters.ofFamily_lwe` and
`Parameters.ofFamily_width`, and the family's `dimension_le`. -/
theorem Parameters.ofFamily_columns_le (F : LWE.Family) (κ : ℕ) :
    (Parameters.ofFamily F κ).columns ≤ (F.dimensionBound.eval κ + 1) * F.residueBits.eval κ := by
  rw [Parameters.columns_eq, Parameters.ofFamily_lwe, Parameters.ofFamily_width]
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (F.dimension_le κ) 1)

/-! ### Targets G16–G17 -/

/-- **G16. The bootstrapped noise is polynomial in the noise bound.** For every family `F`,
noise bound `B` and `κ`, with `P = ofFamily F κ`, `ℓ = P.width` and `m = P.lwe.samples`,
`8 * (P.width * bootNoise P (P.lwe.samples * B κ)) ≤ (pBoot F).eval κ * B κ`
[BV14, Thm 3.7, p016-b001, worst-case analogue]. Deviation: the factor `8` (r3: `4`), see the
module docstring.

**Proof sketch.** `bootNoise_le` (G13) at `β = m·B`. Read `P` through
`Parameters.ofFamily_lwe`, `Parameters.ofFamily_width`, and `pBoot` through `pBoot_eq` and the
`PolyExpr.eval_*` equations. Bound `m ≤ s(κ)` by the family's `samples_le`, and
`N = (n + 1)·ℓ ≤ N̂` by `Parameters.ofFamily_columns_le` (`Parameters.columns_eq` with
`dimension_le`); `⌈log₂ N⌉ ≤ N` (`Nat.clog_le_iff_le_pow` with `N < 2^N`,
`Nat.lt_two_pow_self`), so `X ≤ ℓ + N̂ + 3`; then `8·4^33·2 = 2^70` (`ring`) and monotonicity
of products and powers (`gcongr`: `Nat.mul_le_mul`, `Nat.pow_le_pow_left`). -/
theorem bootRatio_le_poly (F : LWE.Family) (B : ℕ → ℕ) (κ : ℕ) :
    8 * ((Parameters.ofFamily F κ).width *
        bootNoise (Parameters.ofFamily F κ) ((Parameters.ofFamily F κ).lwe.samples * B κ)) ≤
      (pBoot F).eval κ * B κ := by
  -- Step 1: the readers of `ofFamily` and the family's bounds, `ℓ = r(κ)`, `m ≤ s(κ)`, `N ≤ N̂`.
  have hw : (Parameters.ofFamily F κ).width = F.residueBits.eval κ :=
    Parameters.ofFamily_width F κ
  have hm : (Parameters.ofFamily F κ).lwe.samples ≤ F.samplesBound.eval κ := by
    rw [Parameters.ofFamily_lwe]
    exact F.samples_le κ
  have hN := Parameters.ofFamily_columns_le F κ
  -- Step 2: `⌈log₂ N⌉ ≤ N ≤ N̂`.
  have hlog : Nat.clog 2 (Parameters.ofFamily F κ).columns ≤
      (F.dimensionBound.eval κ + 1) * F.residueBits.eval κ :=
    ((Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le).trans hN
  -- Step 3: G13 at `β = m·B`, the constant `8·4^33·2 = 2^70`, and monotonicity.
  have hboot := bootNoise_le (Parameters.ofFamily F κ)
    ((Parameters.ofFamily F κ).lwe.samples * B κ)
  rw [pBoot_eq]
  simp only [PolyExpr.eval_mul, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_const]
  set P := Parameters.ofFamily F κ
  calc 8 * (P.width * bootNoise P (P.lwe.samples * B κ))
      ≤ 8 * (P.width * (4 ^ 33 * P.columns ^ 19 * (P.width + Nat.clog 2 P.columns + 3) ^ 4 *
          (2 * (P.lwe.samples * B κ)))) := by gcongr
    _ = 2 ^ 70 * P.width * P.columns ^ 19 * (P.width + Nat.clog 2 P.columns + 3) ^ 4 *
          P.lwe.samples * B κ := by ring
    _ ≤ _ := by rw [hw]; gcongr

/-- **The decryption condition at a polynomial ratio.** Glue. For every family `F`, noise bound
`B` and `κ` with `pBoot(κ)·B(κ) < q(κ)` (`hq`), every `y` at most the bootstrapped noise
`bootNoise P (m·B κ)` at `P = ofFamily F κ` satisfies
`2 * (P.width * y) < P.lwe.modulus / 2`: G16 gives `8·(ℓ·y) < q`, and `q ≥ 2`. -/
private theorem two_mul_width_lt_of_ratio (F : LWE.Family) (B : ℕ → ℕ) (κ : ℕ)
    (hq : (pBoot F).eval κ * B κ < (F.parameters κ).modulus) {y : ℕ}
    (hy : y ≤ bootNoise (Parameters.ofFamily F κ)
      ((Parameters.ofFamily F κ).lwe.samples * B κ)) :
    2 * ((Parameters.ofFamily F κ).width * y) < (Parameters.ofFamily F κ).lwe.modulus / 2 := by
  have h16 := bootRatio_le_poly F B κ
  have hy' := Nat.mul_le_mul_left (Parameters.ofFamily F κ).width hy
  have h2 := (F.parameters κ).modulus_ge_two
  rw [Parameters.ofFamily_lwe]
  omega

/-- **G17, pure scheme. Correctness at a polynomial ratio.** For every family `F`, noise bound
`B` and `κ`, if the noise law `F.noise κ` is `B κ`-bounded and `pBoot(κ)·B(κ) < q(κ)`, then
the pure bootstrapped GSW at `P = ofFamily F κ` decrypts every fan-in-2 circuit correctly, for
every key seed `rg`, evaluation-key coins `R`, input bits `x` and coins `R'`:
`decrypt P sk (fheEvalCircuit P (evalKey P pk sk R) Cc hC fun j => encrypt P pk (x j) (R' j)) =
Cc.eval x` with `(pk, sk) = Regev.keygen P.lwe (F.noise κ) rg` [BV14, §3.4, Thm 3.7,
p016-b001]. With `LWE.Family.RatioBounded F B p` (`ratioBounded_iff`) this is the regime of a
polynomial ratio. Deviation: worst case.

**Proof sketch.** G12 (`decrypt_keygen_fheEvalCircuit`) at `P`. Its condition
`2·(ℓ·bootNoise P (m·B κ)) < ⌊q/2⌋` follows from G16 (`bootRatio_le_poly`) and `hq` (the
private glue `two_mul_width_lt_of_ratio`): `8·y ≤ pBoot(κ)·B(κ) < q` gives `4·y + 2 ≤ q` when
`y ≥ 1` (and trivially when `y = 0`, as `q ≥ 2`), hence `2·y < ⌊q/2⌋` (`omega`), with
`y = ℓ·bootNoise`. `q` is read as `(ofFamily F κ).lwe.modulus` through
`Parameters.ofFamily_lwe`. -/
theorem decrypt_fheEval_of_ratio (F : LWE.Family) (B : ℕ → ℕ) (κ : ℕ)
    (hχ : (F.noise κ).Bounded (B κ)) (hq : (pBoot F).eval κ * B κ < (F.parameters κ).modulus)
    (rg : KeySeed (Parameters.ofFamily F κ) (F.noise κ))
    (R : Fin (Parameters.ofFamily F κ).columns → Coins (Parameters.ofFamily F κ)) {k : ℕ}
    (Cc : BoolCircuit.DAGCircuit k) (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (x : Fin k → Bool)
    (R' : Fin k → Coins (Parameters.ofFamily F κ)) :
    decrypt (Parameters.ofFamily F κ)
        (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) rg).2
        (fheEvalCircuit (Parameters.ofFamily F κ)
          (evalKey (Parameters.ofFamily F κ)
            (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) rg).1
            (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) rg).2 R) Cc hC
          fun j => encrypt (Parameters.ofFamily F κ)
            (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) rg).1 (x j) (R' j)) =
      Cc.eval x := by
  exact decrypt_keygen_fheEvalCircuit (Parameters.ofFamily F κ) (F.noise κ) rg (B κ) hχ R Cc hC x
    R' (two_mul_width_lt_of_ratio F B κ hq le_rfl)

/-- **G17, leveled scheme. Correctness at a polynomial ratio.** For every family `F`, noise
bound `B`, `κ` and level count `L`, if the noise law is `B κ`-bounded and
`pBoot(κ)·B(κ) < q(κ)`, then the leveled bootstrapped GSW at `P = ofFamily F κ` decrypts, under
the secret of the output level, every fan-in-2 circuit on `k ≥ 1` inputs whose NAND form has
depth at most `L`, for every family of key seeds `rgs`, level coins `R`, input bits `x` and
coins `R'` [BV14, §3.4, Thm 3.7, p016-b001; BV11, Thm 3.1, Def 3.6, p015-b001, p014-b001].
Deviations: worst case; the public output level; reconstruction disclosed (module docstring).

**Proof sketch.** L3 (`decrypt_keygen_leveledEvalCircuit`) at `P`. Its two conditions follow
from G16 (`bootRatio_le_poly`) and `hq` as in `decrypt_fheEval_of_ratio`
(`two_mul_width_lt_of_ratio` at `y = bootNoise P (m·B)` and at `y = m·B`); the input condition
because `m·B ≤ bootNoise P (m·B)` (`bootNoise_eq`, `N ≥ 1` by `Parameters.neZero_columns`). -/
theorem decrypt_leveledEval_of_ratio (F : LWE.Family) (B : ℕ → ℕ) (κ : ℕ)
    (hχ : (F.noise κ).Bounded (B κ)) (hq : (pBoot F).eval κ * B κ < (F.parameters κ).modulus)
    {L k : ℕ} [NeZero k] (rgs : Fin (L + 1) → KeySeed (Parameters.ofFamily F κ) (F.noise κ))
    (R : LevelCoins (Parameters.ofFamily F κ) L) (Cc : BoolCircuit.DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (hdepth : (Cc.toNANDForm hC).depth ≤ L)
    (x : Fin k → Bool) (R' : Fin k → Coins (Parameters.ofFamily F κ)) :
    decrypt (Parameters.ofFamily F κ)
        (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ)
          (rgs ⟨(Cc.toNANDForm hC).depth, Nat.lt_succ_of_le hdepth⟩)).2
        (leveledEvalCircuit (Parameters.ofFamily F κ)
          (levelKey (Parameters.ofFamily F κ)
            (fun e => (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) (rgs e)).1)
            (fun e => (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) (rgs e)).2) R)
          Cc hC fun j => encrypt (Parameters.ofFamily F κ)
            (Regev.keygen (Parameters.ofFamily F κ).lwe (F.noise κ) (rgs 0)).1 (x j) (R' j)) =
      Cc.eval x := by
  -- The input noise `m·B` is at most `bootNoise P (m·B) = 4^(decDepth P + 1)·(2·(N·(m·B)))`.
  have hin : (Parameters.ofFamily F κ).lwe.samples * B κ ≤
      bootNoise (Parameters.ofFamily F κ) ((Parameters.ofFamily F κ).lwe.samples * B κ) := by
    rw [bootNoise_eq]
    have hN := Nat.pos_of_neZero (Parameters.ofFamily F κ).columns
    calc (Parameters.ofFamily F κ).lwe.samples * B κ
        ≤ 1 * (2 * ((Parameters.ofFamily F κ).columns *
            ((Parameters.ofFamily F κ).lwe.samples * B κ))) := by
          rw [one_mul]
          exact (Nat.le_mul_of_pos_left _ hN).trans (Nat.le_mul_of_pos_left _ two_pos)
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ (by norm_num))
  exact decrypt_keygen_leveledEvalCircuit (Parameters.ofFamily F κ) (F.noise κ) (B κ) hχ rgs R Cc
    hC hdepth x R' (two_mul_width_lt_of_ratio F B κ hq le_rfl)
    (two_mul_width_lt_of_ratio F B κ hq hin)

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW


/-! Liveness pair (gsw-6b-u18-u19, C6, owner PolyRatio.lean), appended to the owner's own probe: a
foreign definition read by `rfl` (negative: closes unsealed, fails exactly once sealed) and the
same fact through its published reader (positive: closes sealed). -/

-- NEG bootNoise by rfl
example (P : TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters) (β : ℕ) :
    TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootNoise P β = 4 ^ (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decDepth P + 1) * (2 * (P.columns * β)) :=
  rfl
-- POS bootNoise through bootNoise_eq
example (P : TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters) (β : ℕ) :
    TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootNoise P β = 4 ^ (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decDepth P + 1) * (2 * (P.columns * β)) :=
  TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootNoise_eq P β

