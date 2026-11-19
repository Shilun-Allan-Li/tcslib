/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic security of public-key, pure and leveled GSW-FHE

## Main definitions

* `encodeCiphertext`, `encodeView`, `encodeFheView`, `encodeLeveledView`: canonical bit
  encodings, built from `LWE.encodeChallenge` (public keys) and
  `Encoding.Modular.encodeMatrix` (ciphertexts), with `_eq` and `_length` readers.
* `WeakCircularSecureFamily F`: the headline hypothesis (A1), every non-uniform PPT
  distinguisher has negligible advantage on the encoded FHE views.
* `ReductionEfficient F`, `LeveledReductionEfficient F L`: the explicit reduction-efficiency
  hypotheses (A4), domination statements, not machine constructions.

## Main results

* `indCPA_of_dlweAssumption` (A1): asymptotic IND-CPA of public-key GSW (the view without the
  evaluation key) from `DLWEAssumption F` and (A4).
* `leveledINDCPA_of_dlweAssumption` (A3): asymptotic IND-CPA of leveled GSW-FHE from
  `DLWEAssumption F` and (A4), with no circular-security assumption.

Both are proved here. Ruling Q-6B-1 A: r3's A2 (`fheView_negligible`) is
not a theorem; the reader `weakCircularSecureFamily_iff` is that statement, the pure-FHE reading
of the hypothesis [BV11, Thm 3.2; BV14, Thm 2.14 second part]: pure-FHE security *is* (A1).

**Compactness** holds by typing (`GSW/Bootstrap.lean`, `GSW/Leveled.lean`).

**Sources and reconstruction (P6-Q19 B), for the leveled statements** (`LeveledReductionEfficient`,
A3). The key chain is Gentry's [Gen09, §4.1, `KeyGen` of `E^(d)`, pp. 46–47, p056-b003], with
his reverse order of the levels undone (`GSW/Leveled.lean`). The level hybrid of L4–L5 follows
[Gen09, Thm 4.2.3 and its proof, pp. 50–51, p060-b001, p061-b001] (`GSW/LeveledSecurity.lean`),
whose reduction loses the factor `ℓ(d + 1)` (Gentry's `ℓ` is the key length), linear in the
depth; here the number of levels `L(κ)` is a polynomial.

## References

* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.1, Thm 3.1, Thm 3.2,
  Def 3.8.
* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Thm 2.14, Thm 3.7.
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
  8 June 2013: §3.2.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, §5.4.3.
* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
  September 2009: §4.1, Thm 4.2.3.

**Deviations.** The asymptotic statements are over an `LWE.Family` with
`P_κ = Parameters.ofFamily F κ` and the canonical encodings above. Machine efficiency of GSW
encryption is not proved: there is no machine-level GSW encryptor (out of scope, as for phase 5),
so the encryption reductions are covered by the explicit hypotheses (A4), stated as domination of
real-valued advantages, which needs no transport between `(ofFamily F κ).lwe` and
`F.parameters κ`.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Complexity
open Encryption.PublicKey

/-! ### Encodings -/

/-- The canonical bit encoding of a ciphertext: its `(n+1) × N` entries row by row, `ℓ` bits
each, `encodeCiphertext P C = Encoding.Modular.encodeMatrix P.width C`. Glue: a local
encoding choice, which the cited sources do not fix. Each entry is written as the `ℓ`-bit binary
numeral of its canonical residue in `{0, …, q − 1}`, the base-two representation of the
canonical representative in [Pei16, §5.4.3, p052-b001]. -/
def encodeCiphertext (P : Parameters) (C : Ciphertext P) : List Bool :=
  Encoding.Modular.encodeMatrix P.width C

/-- `encodeCiphertext P C` is `Encoding.Modular.encodeMatrix P.width C`. -/
theorem encodeCiphertext_eq (P : Parameters) (C : Ciphertext P) :
    encodeCiphertext P C = Encoding.Modular.encodeMatrix P.width C := rfl

/-- An encoded ciphertext has `(n + 1)·N·ℓ` bits:
`(encodeCiphertext P C).length = (P.lwe.dimension + 1) * P.columns * P.width`. -/
theorem encodeCiphertext_length (P : Parameters) (C : Ciphertext P) :
    (encodeCiphertext P C).length = (P.lwe.dimension + 1) * P.columns * P.width := by
  rw [encodeCiphertext_eq, Encoding.Modular.encodeMatrix_length]

/-- The canonical encoding of a phase-5 view `(pk, ct)`: the public key as an LWE challenge
(`LWE.encodeChallenge`, width `ℓ`) followed by the ciphertext,
`encodeView P v = LWE.encodeChallenge P.lwe P.width v.1 ++ encodeCiphertext P v.2`. -/
def encodeView (P : Parameters) (v : PublicKey P × Ciphertext P) : List Bool :=
  LWE.encodeChallenge P.lwe P.width v.1 ++ encodeCiphertext P v.2

/-- `encodeView P v` is `LWE.encodeChallenge P.lwe P.width v.1 ++ encodeCiphertext P v.2`. -/
theorem encodeView_eq (P : Parameters) (v : PublicKey P × Ciphertext P) :
    encodeView P v = LWE.encodeChallenge P.lwe P.width v.1 ++ encodeCiphertext P v.2 := rfl

/-- An encoded view has `m·(n + 1)·ℓ + (n + 1)·N·ℓ` bits. -/
theorem encodeView_length (P : Parameters) (v : PublicKey P × Ciphertext P) :
    (encodeView P v).length =
      P.lwe.samples * (P.lwe.dimension + 1) * P.width +
        (P.lwe.dimension + 1) * P.columns * P.width := by
  rw [encodeView_eq, List.length_append, LWE.encodeChallenge_length, encodeCiphertext_length]

/-- The canonical encoding of an FHE view `(pk, evk, ct)`: the public key, the `N`
evaluation-key ciphertexts in order, and the challenge,
`encodeFheView P v = LWE.encodeChallenge P.lwe P.width v.1 ++
(List.ofFn fun i => encodeCiphertext P (v.2.1 i)).flatten ++ encodeCiphertext P v.2.2`. -/
def encodeFheView (P : Parameters) (v : FheView P) : List Bool :=
  LWE.encodeChallenge P.lwe P.width v.1 ++
    (List.ofFn fun i => encodeCiphertext P (v.2.1 i)).flatten ++ encodeCiphertext P v.2.2

/-- `encodeFheView P v` is `LWE.encodeChallenge P.lwe P.width v.1 ++
(List.ofFn fun i => encodeCiphertext P (v.2.1 i)).flatten ++ encodeCiphertext P v.2.2`. -/
theorem encodeFheView_eq (P : Parameters) (v : FheView P) :
    encodeFheView P v =
      LWE.encodeChallenge P.lwe P.width v.1 ++
        (List.ofFn fun i => encodeCiphertext P (v.2.1 i)).flatten ++ encodeCiphertext P v.2.2 :=
  rfl

/-- An encoded FHE view has `m·(n + 1)·ℓ + N·((n + 1)·N·ℓ) + (n + 1)·N·ℓ` bits. -/
theorem encodeFheView_length (P : Parameters) (v : FheView P) :
    (encodeFheView P v).length =
      P.lwe.samples * (P.lwe.dimension + 1) * P.width +
        P.columns * ((P.lwe.dimension + 1) * P.columns * P.width) +
        (P.lwe.dimension + 1) * P.columns * P.width := by
  rw [encodeFheView_eq, List.length_append, List.length_append, LWE.encodeChallenge_length,
    encodeCiphertext_length, List.ofFn_eq_map,
    length_flatten_map_const (List.finRange P.columns) _ _
      fun i => encodeCiphertext_length P (v.2.1 i),
    List.length_finRange]

/-- The canonical encoding of a leveled view: the `L + 1` public keys, the `L` level keys of
`N` ciphertexts each (level by level, position by position), and the challenge,
`encodeLeveledView P L v = (List.ofFn fun d => LWE.encodeChallenge P.lwe P.width (v.1 d)).flatten
++ (List.ofFn fun e => (List.ofFn fun j => encodeCiphertext P (v.2.1 e j)).flatten).flatten ++
encodeCiphertext P v.2.2`. -/
def encodeLeveledView (P : Parameters) (L : ℕ) (v : LeveledView P L) : List Bool :=
  (List.ofFn fun d => LWE.encodeChallenge P.lwe P.width (v.1 d)).flatten ++
    (List.ofFn fun e => (List.ofFn fun j => encodeCiphertext P (v.2.1 e j)).flatten).flatten ++
    encodeCiphertext P v.2.2

/-- `encodeLeveledView P L v` is the concatenation of the encoded public keys, the encoded level
keys and the encoded challenge (the formula of `encodeLeveledView`'s docstring). -/
theorem encodeLeveledView_eq (P : Parameters) (L : ℕ) (v : LeveledView P L) :
    encodeLeveledView P L v =
      (List.ofFn fun d => LWE.encodeChallenge P.lwe P.width (v.1 d)).flatten ++
        (List.ofFn fun e => (List.ofFn fun j => encodeCiphertext P (v.2.1 e j)).flatten).flatten ++
        encodeCiphertext P v.2.2 := rfl

/-- An encoded leveled view has `(L + 1)·(m·(n + 1)·ℓ) + L·(N·((n + 1)·N·ℓ)) + (n + 1)·N·ℓ`
bits. -/
theorem encodeLeveledView_length (P : Parameters) (L : ℕ) (v : LeveledView P L) :
    (encodeLeveledView P L v).length =
      (L + 1) * (P.lwe.samples * (P.lwe.dimension + 1) * P.width) +
        L * (P.columns * ((P.lwe.dimension + 1) * P.columns * P.width)) +
        (P.lwe.dimension + 1) * P.columns * P.width := by
  have hcts : ∀ (n : ℕ) (f : Fin n → Ciphertext P),
      (List.ofFn fun j => encodeCiphertext P (f j)).flatten.length =
        n * ((P.lwe.dimension + 1) * P.columns * P.width) := fun n f => by
    rw [List.ofFn_eq_map, length_flatten_map_const (List.finRange n) _ _
      fun j => encodeCiphertext_length P (f j), List.length_finRange]
  rw [encodeLeveledView_eq, List.length_append, List.length_append, encodeCiphertext_length,
    List.ofFn_eq_map,
    length_flatten_map_const (List.finRange (L + 1)) _ _
      fun d => LWE.encodeChallenge_length P.lwe P.width (v.1 d),
    List.ofFn_eq_map,
    length_flatten_map_const (List.finRange L) _ _ fun e => hcts P.columns (v.2.1 e),
    List.length_finRange, List.length_finRange]

/-! ### The asymptotic hypotheses -/

/-- **Weak circular security, asymptotic: the headline hypothesis** (A1; P6-Q15 A)
[BV11, Def 3.8 with Def 3.1, p015-b001, p013-b002; BV14, Thm 2.14, p008-b003]: every
non-uniform PPT distinguisher `D` has negligible advantage between the encoded FHE views of `0`
and `1` at `P_κ = Parameters.ofFamily F κ`,
`WeakCircularSecureFamily F ↔ ∀ D : NUPPT, Negligible fun κ => distAdv
(fheView P_κ (F.noise κ) false) (fheView P_κ (F.noise κ) true)
(fun v r => D.distinguisherL κ (encodeFheView P_κ v) r)`. Equivalently, each `D` satisfies the
concrete `WeakCircularSecure` at every `κ` with a negligible `ε`. Its reader
`weakCircularSecureFamily_iff` is r3's A2, the pure-FHE security statement [BV11, Thm 3.2,
p015-b001; BV14, Thm 2.14 second part, p008-b003] (ruling Q-6B-1 A). A hypothesis, never derived
from LWE. -/
def WeakCircularSecureFamily (F : LWE.Family) : Prop :=
  ∀ D : NUPPT, Negligible fun κ =>
    distAdv (fheView (Parameters.ofFamily F κ) (F.noise κ) false)
      (fheView (Parameters.ofFamily F κ) (F.noise κ) true)
      (fun v r => D.distinguisherL κ (encodeFheView (Parameters.ofFamily F κ) v) r)

/-- `WeakCircularSecureFamily F` holds exactly when every `D : NUPPT` has negligible advantage
`distAdv (fheView P_κ (F.noise κ) false) (fheView P_κ (F.noise κ) true)
(fun v r => D.distinguisherL κ (encodeFheView P_κ v) r)`, `P_κ = Parameters.ofFamily F κ`. This
reader is r3's A2 (Q-6B-1 A). -/
theorem weakCircularSecureFamily_iff (F : LWE.Family) :
    WeakCircularSecureFamily F ↔ ∀ D : NUPPT, Negligible fun κ =>
      distAdv (fheView (Parameters.ofFamily F κ) (F.noise κ) false)
        (fheView (Parameters.ofFamily F κ) (F.noise κ) true)
        (fun v r => D.distinguisherL κ (encodeFheView (Parameters.ofFamily F κ) v) r) :=
  Iff.rfl

/-- **(A4) Reduction efficiency, explicit hypothesis** (P6-Q10): for every non-uniform PPT
distinguisher `D` of encoded phase-5 views and every bit `μ`, some non-uniform PPT `D'` has, at
every `κ`, DLWE advantage at least that of phase 5's encryption reduction run on `D`,
`decisionAdvantage P_κ.lwe χ_κ (reduction P_κ μ D_κ) ≤ F.advantageAt D' κ`, with
`P_κ = ofFamily F κ`, `χ_κ = F.noise κ` and `D_κ v r = D.distinguisherL κ (encodeView P_κ v) r`
[GSW13, §3.2, Lemma 1, p009-b002, p010-b001]. It says that encrypting a fixed bit under the
challenge key with fresh binary coins, re-encoding and running `D` is polynomial-time. A
domination statement, not a machine construction: the library has no machine-level GSW
encryptor (out of scope, as for phase 5). Real-valued on both sides, so no transport between
`(ofFamily F κ).lwe` and `F.parameters κ` is needed. -/
def ReductionEfficient (F : LWE.Family) : Prop :=
  ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
    LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
        (reduction (Parameters.ofFamily F κ) μ fun v r =>
          D.distinguisherL κ (encodeView (Parameters.ofFamily F κ) v) r) ≤
      F.advantageAt D' κ

/-- `ReductionEfficient F` holds exactly when for every `D : NUPPT` and `μ` some `D' : NUPPT`
has `decisionAdvantage P_κ.lwe (F.noise κ) (reduction P_κ μ D_κ) ≤ F.advantageAt D' κ` at every
`κ` (the formula of `ReductionEfficient`'s docstring). -/
theorem reductionEfficient_iff (F : LWE.Family) :
    ReductionEfficient F ↔ ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
      LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
          (reduction (Parameters.ofFamily F κ) μ fun v r =>
            D.distinguisherL κ (encodeView (Parameters.ofFamily F κ) v) r) ≤
        F.advantageAt D' κ :=
  Iff.rfl

/-- **(A4) for the leveled hybrid** (P6-Q10, P6-Q11): for every non-uniform PPT distinguisher
`D` of encoded leveled views (`L(κ)` levels) and every bit `μ`, one non-uniform PPT `D'`
dominates, at every `κ`, the DLWE advantages of every level reduction
`levelReduction P_κ χ_κ L(κ) μ e j b D_κ` (every level `e`, position `j` and side `b`, L4) and
of the challenge reductions `reduction P_κ μ' (challengeDist P_κ χ_κ L(κ) D_κ)` (L5), with
`D_κ v r = D.distinguisherL κ (encodeLeveledView P_κ L(κ) v) r`. One `D'` serves every
`(e, j, b)`: non-uniform advice can select the worst one at each `κ` (r3 §H8 item 13). A
domination statement, not a construction; real-valued, so no type-level transport. Deviation: r3
names only the level reductions; the challenge reductions of L5's last step are added, since A3
needs them. Reconstruction disclosed (module docstring). -/
def LeveledReductionEfficient (F : LWE.Family) (L : PolyExpr) : Prop :=
  ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
    (∀ (e : Fin (L.eval κ)) (j : Fin (Parameters.ofFamily F κ).columns) (b : Bool),
      LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
          (levelReduction (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) μ e j b fun v r =>
            D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v) r) ≤
        F.advantageAt D' κ) ∧
    ∀ μ' : Bool,
      LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
          (reduction (Parameters.ofFamily F κ) μ'
            (challengeDist (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) fun v r =>
              D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v) r)) ≤
        F.advantageAt D' κ

/-- `LeveledReductionEfficient F L` holds exactly when for every `D : NUPPT` and `μ` some
`D' : NUPPT` dominates at every `κ` the DLWE advantages of every level reduction and of the
challenge reductions (the formula of `LeveledReductionEfficient`'s docstring). -/
theorem leveledReductionEfficient_iff (F : LWE.Family) (L : PolyExpr) :
    LeveledReductionEfficient F L ↔ ∀ (D : NUPPT) (μ : Bool), ∃ D' : NUPPT, ∀ κ,
      (∀ (e : Fin (L.eval κ)) (j : Fin (Parameters.ofFamily F κ).columns) (b : Bool),
        LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
            (levelReduction (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) μ e j b fun v r =>
              D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v) r) ≤
          F.advantageAt D' κ) ∧
      ∀ μ' : Bool,
        LWE.decisionAdvantage (Parameters.ofFamily F κ).lwe (F.noise κ)
            (reduction (Parameters.ofFamily F κ) μ'
              (challengeDist (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) fun v r =>
                D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v)
                  r)) ≤
          F.advantageAt D' κ :=
  Iff.rfl

/-! ### Targets A1, A3 -/

/-- **A1. Asymptotic IND-CPA of public-key GSW** (the view without the evaluation key): for an
LWE family `F` with `DLWEAssumption F`, the reduction-efficiency hypothesis (A4) and the width
condition `(n + 1)·ℓ + 2κ ≤ m` at every `κ`, every non-uniform PPT `D` has negligible advantage
between the encoded real views of `false` and `true` at `P_κ = ofFamily F κ`,
`Negligible fun κ => distAdv (realView P_κ (F.noise κ) false) (realView P_κ (F.noise κ) true)
(fun v r => D.distinguisherL κ (encodeView P_κ v) r)` [GSW13, §3.2, p009-b002; BV11, Def 3.1,
p013-b002]. Deviation: concrete reductions covered by (A4).

**Proof sketch.** At each `κ`, phase 5's `distAdv_encrypt_le_of_width` with `w = ℓ`
(`q ≤ 2^ℓ` by the family's `modulus_le_pow`, `hm` read through `Parameters.ofFamily_lwe` and
`Parameters.ofFamily_width`) bounds the advantage by the two DLWE advantages of `reduction`
plus `N·2^{−κ}`. `heff` (`reductionEfficient_iff`) gives `D'₀`, `D'₁` dominating them by
`F.advantageAt D'ᵢ κ`, negligible by `dlweAssumption_iff`. `N = (n + 1)·ℓ` is at most
`(d(κ) + 1)·ℓ(κ)` (`dimension_le`, `PolyExpr.eval`), so `negligible_polyExpr_mul`
(`Asymptotic/EnsemblesLemmas.lean`) with `negligible_two_pow_neg` makes the last term negligible;
`Negligible.add` and `Negligible.mono` (`distAdv` is nonnegative) finish. -/
theorem indCPA_of_dlweAssumption (F : LWE.Family) (hF : LWE.DLWEAssumption F)
    (heff : ReductionEfficient F)
    (hm : ∀ κ, ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤
      (F.parameters κ).samples)
    (D : NUPPT) :
    Negligible fun κ =>
      distAdv (realView (Parameters.ofFamily F κ) (F.noise κ) false)
        (realView (Parameters.ofFamily F κ) (F.noise κ) true)
        (fun v r => D.distinguisherL κ (encodeView (Parameters.ofFamily F κ) v) r) := by
  -- Step 1: (A4) at `μ = false, true` gives `D'₀`, `D'₁`, whose advantages are negligible.
  obtain ⟨D₀, hD₀⟩ := (reductionEfficient_iff F).1 heff D false
  obtain ⟨D₁, hD₁⟩ := (reductionEfficient_iff F).1 heff D true
  have hneg₀ := (LWE.dlweAssumption_iff F).1 hF D₀
  have hneg₁ := (LWE.dlweAssumption_iff F).1 hF D₁
  -- Step 2: the statistical term `N̂(κ)·2^{−κ}` with `N̂ = (d + 1)·r` is negligible.
  have hstat := EnsembleLemmas.negligible_polyExpr_mul
    (.mul (.add F.dimensionBound (.const 1)) F.residueBits) negligible_two_pow_neg
  refine ((hneg₀.add hneg₁).add hstat).mono ⟨0, fun κ _ => ?_⟩
  -- Step 3: phase 5's concrete bound at `κ` with width `r(κ)`, read through `ofFamily_lwe`.
  have hq : (Parameters.ofFamily F κ).lwe.modulus ≤ 2 ^ F.residueBits.eval κ := by
    rw [Parameters.ofFamily_lwe]
    exact F.modulus_le_pow κ
  have hmκ : ((Parameters.ofFamily F κ).lwe.dimension + 1) * F.residueBits.eval κ + 2 * κ ≤
      (Parameters.ofFamily F κ).lwe.samples := by
    rw [Parameters.ofFamily_lwe]
    exact hm κ
  have hbound := distAdv_encrypt_le_of_width (Parameters.ofFamily F κ) (F.noise κ) false true
    (F.residueBits.eval κ) κ hq hmκ
    (fun v r => D.distinguisherL κ (encodeView (Parameters.ofFamily F κ) v) r)
  -- Step 4: `N ≤ N̂(κ)` (`Parameters.ofFamily_columns_le`), and `distAdv ≥ 0`.
  have hN : ((Parameters.ofFamily F κ).columns : ℝ) * (2 : ℝ)⁻¹ ^ κ ≤
      ((PolyExpr.mul (.add F.dimensionBound (.const 1)) F.residueBits).eval κ : ℝ) *
        (2 : ℝ)⁻¹ ^ κ := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Parameters.ofFamily_columns_le F κ)
      (by positivity)
  have h0 : 0 ≤ distAdv (realView (Parameters.ofFamily F κ) (F.noise κ) false)
      (realView (Parameters.ofFamily F κ) (F.noise κ) true)
      (fun v r => D.distinguisherL κ (encodeView (Parameters.ofFamily F κ) v) r) := by
    rw [distAdv_def]
    exact abs_nonneg _
  rw [abs_of_nonneg h0]
  refine le_trans ?_ (le_abs_self _)
  linarith only [hbound, hD₀ κ, hD₁ κ, hN]

/-- **A3. Asymptotic IND-CPA of leveled GSW-FHE from DLWE**: for an LWE family `F` with
`DLWEAssumption F`, a polynomial number of levels `L`, the leveled reduction-efficiency
hypothesis (A4) and the width condition at every `κ`, every non-uniform PPT `D` has negligible
advantage between the encoded leveled views of `false` and `true` at `P_κ = ofFamily F κ` with
`L(κ)` levels,
`Negligible fun κ => distAdv (leveledView P_κ (F.noise κ) (L.eval κ) false)
(leveledView P_κ (F.noise κ) (L.eval κ) true)
(fun v r => D.distinguisherL κ (encodeLeveledView P_κ (L.eval κ) v) r)` [BV14, Thm 3.7,
p016-b001; BV11, Thm 3.1, p015-b001]. No circular-security assumption. Reconstruction
disclosed (module docstring).

**Proof sketch.** At each `κ`, L5 (`distAdv_leveledView_le`) bounds the advantage by
`∑_{e < L(κ)} ∑_{j < N} (levelTerm₀ + levelTerm₁) + challengeTerm`. `heff`
(`leveledReductionEfficient_iff`) for `μ = false` and `μ = true` gives `D'₀`, `D'₁` dominating
every DLWE advantage in `levelTerm_eq` and `challengeTerm_eq`; `Regev.two_extractionError_le`
with `hm` bounds `2·ε_LHL ≤ 2^{−κ}`. So the bound is at most
`(2·L(κ)·N + 1)·(2·(advantageAt D'₀ κ + advantageAt D'₁ κ) + N·2^{−κ})`, a polynomial
(`(d(κ) + 1)·ℓ(κ)` bounds `N`; `PolyExpr.eval`) times negligible functions
(`dlweAssumption_iff`, `negligible_two_pow_neg`, `negligible_polyExpr_mul` from
`Asymptotic/EnsemblesLemmas.lean`, `Negligible.add`, `Negligible.mono`). -/
theorem leveledINDCPA_of_dlweAssumption (F : LWE.Family) (L : PolyExpr)
    (hF : LWE.DLWEAssumption F) (heff : LeveledReductionEfficient F L)
    (hm : ∀ κ, ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤
      (F.parameters κ).samples)
    (D : NUPPT) :
    Negligible fun κ =>
      distAdv (leveledView (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) false)
        (leveledView (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) true)
        (fun v r => D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v)
          r) := by
  -- Step 1: (A4) at `μ = false, true` gives `D'₀`, `D'₁`, whose advantages are negligible.
  obtain ⟨D₀, hD₀⟩ := (leveledReductionEfficient_iff F L).1 heff D false
  obtain ⟨D₁, hD₁⟩ := (leveledReductionEfficient_iff F L).1 heff D true
  have hneg₀ := (LWE.dlweAssumption_iff F).1 hF D₀
  have hneg₁ := (LWE.dlweAssumption_iff F).1 hF D₁
  -- Step 2: `(2·L·N̂ + 1)·(2·(adv D'₀ + adv D'₁) + N̂·2^{−κ})` is negligible, `N̂ = (d + 1)·r`.
  have hstat := EnsembleLemmas.negligible_polyExpr_mul
    (.mul (.add F.dimensionBound (.const 1)) F.residueBits) negligible_two_pow_neg
  have hinner := ((hneg₀.add hneg₁).const_mul 2).add hstat
  refine (EnsembleLemmas.negligible_polyExpr_mul
    (.add (.mul (.mul (.const 2) L) (.mul (.add F.dimensionBound (.const 1)) F.residueBits))
      (.const 1)) hinner).mono ⟨0, fun κ _ => ?_⟩
  -- Step 3: L5 at `κ`, and `2·ε_LHL ≤ 2^{−κ}` from `hm`, read through `ofFamily_lwe`.
  have hq : (Parameters.ofFamily F κ).lwe.modulus ≤ 2 ^ F.residueBits.eval κ := by
    rw [Parameters.ofFamily_lwe]
    exact F.modulus_le_pow κ
  have hmκ : ((Parameters.ofFamily F κ).lwe.dimension + 1) * F.residueBits.eval κ + 2 * κ ≤
      (Parameters.ofFamily F κ).lwe.samples := by
    rw [Parameters.ofFamily_lwe]
    exact hm κ
  have hε := Regev.two_extractionError_le (Parameters.ofFamily F κ).lwe (F.residueBits.eval κ) κ
    hq hmκ
  have hNle : ((Parameters.ofFamily F κ).columns : ℝ) ≤
      ((F.dimensionBound.eval κ : ℝ) + 1) * F.residueBits.eval κ := by
    exact_mod_cast Parameters.ofFamily_columns_le F κ
  have hL5 := distAdv_leveledView_le (Parameters.ofFamily F κ) (F.noise κ) (L.eval κ) false true
    (fun v r => D.distinguisherL κ (encodeLeveledView (Parameters.ofFamily F κ) (L.eval κ) v) r)
  obtain ⟨hlev₀, hch₀⟩ := hD₀ κ
  obtain ⟨hlev₁, hch₁⟩ := hD₁ κ
  set P := Parameters.ofFamily F κ
  set N := (P.columns : ℝ)
  set t := (2 : ℝ)⁻¹ ^ κ
  -- Step 4: every level pair is at most `2·(adv D'₀ + adv D'₁) + 2·N·t`, the challenge term at
  -- most `2·adv D'₀ + N·t`; both advantages are nonnegative.
  have hNε : 2 * (N * Regev.extractionError P.lwe) ≤ N * t := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hε (Nat.cast_nonneg _)
  have hpair : ∀ (e : Fin (L.eval κ)) (j : Fin P.columns),
      levelTerm P (F.noise κ) (L.eval κ) false e j
          (fun v r => D.distinguisherL κ (encodeLeveledView P (L.eval κ) v) r) +
        levelTerm P (F.noise κ) (L.eval κ) true e j
          (fun v r => D.distinguisherL κ (encodeLeveledView P (L.eval κ) v) r) ≤
      2 * (F.advantageAt D₀ κ + F.advantageAt D₁ κ) + 2 * (N * t) := fun e j => by
    rw [levelTerm_eq, levelTerm_eq]
    linarith only [hlev₀ e j true, hlev₀ e j false, hlev₁ e j true, hlev₁ e j false, hNε]
  have hsum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpair e j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hch : challengeTerm P (F.noise κ) (L.eval κ) false true
      (fun v r => D.distinguisherL κ (encodeLeveledView P (L.eval κ) v) r) ≤
      2 * F.advantageAt D₀ κ + N * t := by
    rw [challengeTerm_eq]
    linarith only [hch₀ false, hch₀ true, hNε]
  have ha₀ : 0 ≤ F.advantageAt D₀ κ := by
    refine le_trans ?_ (hch₀ false)
    rw [LWE.decisionAdvantage_eq, distAdv_def]
    exact abs_nonneg _
  have ha₁ : 0 ≤ F.advantageAt D₁ κ := by
    refine le_trans ?_ (hch₁ false)
    rw [LWE.decisionAdvantage_eq, distAdv_def]
    exact abs_nonneg _
  -- Step 5: `N ≤ N̂` and the polynomial arithmetic; `distAdv ≥ 0`.
  have h0 : 0 ≤ distAdv (leveledView P (F.noise κ) (L.eval κ) false)
      (leveledView P (F.noise κ) (L.eval κ) true)
      (fun v r => D.distinguisherL κ (encodeLeveledView P (L.eval κ) v) r) := by
    rw [distAdv_def]
    exact abs_nonneg _
  rw [abs_of_nonneg h0]
  refine le_trans ?_ (le_abs_self _)
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  push_cast
  have ht : 0 ≤ t := by positivity
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ L.eval κ := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ ((F.dimensionBound.eval κ : ℝ) + 1) * F.residueBits.eval κ :=
    hN0.trans hNle
  have hA : 0 ≤ F.advantageAt D₀ κ + F.advantageAt D₁ κ := add_nonneg ha₀ ha₁
  have hNt := mul_le_mul_of_nonneg_right hNle ht
  have hmono : (L.eval κ : ℝ) * (N * (2 * (F.advantageAt D₀ κ + F.advantageAt D₁ κ) +
      2 * (N * t))) ≤ (L.eval κ : ℝ) * ((((F.dimensionBound.eval κ : ℝ) + 1) *
        F.residueBits.eval κ) * (2 * (F.advantageAt D₀ κ + F.advantageAt D₁ κ) +
          2 * ((((F.dimensionBound.eval κ : ℝ) + 1) * F.residueBits.eval κ) * t))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hNle (by linarith only [hNt])
      (by linarith only [hA, mul_nonneg hN0 ht]) hM0) hL0
  linarith only [hL5, hsum, hch, hmono, hNt, ha₁, mul_nonneg (mul_nonneg hL0 hM0) hA]

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

set_option pp.fullNames true
set_option pp.funBinderTypes true
#check @TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.indCPA_of_dlweAssumption
#check @TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.leveledINDCPA_of_dlweAssumption
