/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Security
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# IND-CPA of leveled GSW-FHE from DLWE: the top-down key hybrid

## Main definitions

* `LeveledSeeds`, `LeveledView`: the seeds and the view of the leveled scheme.
* `leveledView`: the `L + 1` public keys, the `L` level keys and `Enc_{pk_0}(μ)`.
* `levelHybrid`: the hybrid `H_h` in which the level keys `e ≥ h` encrypt `0` instead of the
  key bits; `H_L` is the real view, `H_0` has no key bits at all.
* `levelMsgs`, `levelAssemble`, `levelReduction`: the reduction of step `e` at position `j`,
  `hybridPlant` (the shared multi-ciphertext hybrid) composed with phase 5's `reduction`.
* `levelTerm`: its two DLWE advantages plus `2·(N·ε_LHL)`.
* `challengeDist`, `challengeTerm`: the final phase-5 step on the challenge under `pk_0`.

## Main results

* `distAdv_levelHybrid_le` (L4): one level, `N` positions.
* `distAdv_leveledView_le` (L5): IND-CPA of leveled GSW-FHE from DLWE.

Both are proved here.

**Sources and reconstruction (P6-Q19 B).** The key chain is Gentry's [Gen09, §4.1, `KeyGen` of
`E^(d)`, pp. 46–47, p056-b003], with his reverse order of the levels undone: his level `i` is
level `L − i` here (`GSW/Leveled.lean`). The hybrid order is his [Gen09, Thm 4.2.3 and its
proof, pp. 50–51, p060-b001, p061-b001]: Game `k` replaces the encryptions under `pk_{i−1}` of
`sk_i` for `i ∈ [1, k]`, and the step from Game `k` to Game `k + 1` plants the challenge key as
`pk_k`, whose secret occurs only in encryptions already replaced. Renumbered, Game `k` is
`H_{L−k}`, and the order is the top-down order below. The statements cite [BV11, Thm 3.1,
Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3], with [GSW13, §3.2, Lemma 1],
[BV11, Def 3.1] and [BV14, §2.5] for the one-key steps and the view; [Gen09] is cited here, for
the construction. Deviations from [Gen09, Thm 4.2.3]: a replaced level key encrypts `0`, not
the bits of an unrelated fresh key; each level step is a hybrid over the `N` positions, not one
challenge of Gentry's `ℓ`-fold scheme `(E)^ℓ`; each step reduces to DLWE (phase 5), not to the
semantic security of the base scheme; and the middle step between the two chains is phase 5's
challenge step, not Gentry's Game `d + 1` (a random plaintext).

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Thm 2.14 (first part), Thm 3.7.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.1, Def 3.6, Thm 3.1.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: §5.3.
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
  8 June 2013: §3.2, Lemma 1.
* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University,
  September 2009: §4.1, Thm 4.2.3 (with its proof).

**Deviations.** Levels are indexed from `0`: the level key `e : Fin L` encrypts the bits of
`s_e` under `pk_{e+1}` (r3's `evk_d`, `d = e + 1`). The hybrid runs top-down: step `e` (from
`H_{e+1}` to `H_e`, `e = L − 1, …, 0`) replaces the level key `e` by encryptions of `0`; it is
legitimate because `s_{e+1}`, the secret of `pk_{e+1}`, occurs only in the level key `e + 1`,
already replaced. Each step is a multi-ciphertext hybrid over the `N` positions; its messages,
the bits of `s_e`, are random and are drawn inside the reduction's coins (r3 §H8 item 12).
The challenge bit `μ` enters each step's reduction (which must simulate the challenge), so the
level terms carry `μ`, and the bound of L5 sums the terms of the two chains (`μ₀` and `μ₁`)
where r3 wrote `2·∑`. Concrete statements with function-level distinguishers, as phase 5.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- The seeds of the leveled view: `L + 1` key-generation seeds, the coins of the `N·L` level-key
encryptions and the coins of the challenge. Reducible notation. -/
abbrev LeveledSeeds (P : Parameters) (χ : LWE.Noise) (L : ℕ) : Type :=
  (Fin (L + 1) → KeySeed P χ) × LevelCoins P L × Coins P

/-- `LeveledSeeds P χ L` is `(Fin (L + 1) → KeySeed P χ) × LevelCoins P L × Coins P`. -/
theorem LeveledSeeds_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) :
    LeveledSeeds P χ L = ((Fin (L + 1) → KeySeed P χ) × LevelCoins P L × Coins P) := rfl

/-- The leveled view: `L + 1` public keys, `L` level keys of `N` ciphertexts each, and one
challenge ciphertext. Reducible notation. -/
abbrev LeveledView (P : Parameters) (L : ℕ) : Type :=
  (Fin (L + 1) → PublicKey P) × (Fin L → Fin P.columns → Ciphertext P) × Ciphertext P

/-- `LeveledView P L` is `(Fin (L + 1) → PublicKey P) × (Fin L → Fin P.columns → Ciphertext P) ×
Ciphertext P`. -/
theorem LeveledView_eq (P : Parameters) (L : ℕ) :
    LeveledView P L =
      ((Fin (L + 1) → PublicKey P) × (Fin L → Fin P.columns → Ciphertext P) × Ciphertext P) :=
  rfl

/-- **The leveled FHE view of a bit** `μ` [BV11, Def 3.1, p013-b002, for the leveled scheme;
BV14, §2.5, p007-b001]: from independent honest key generations
`(pk_d, s_d) = Regev.keygen P.lwe χ (r.1 d)`, the public keys, the chain of level keys
`levelKey P pk s r.2.1` and the challenge `encrypt P pk_0 μ r.2.2`,
`leveledView P χ L μ r = (pk, levelKey P pk s r.2.1, encrypt P (pk 0) μ r.2.2)`.
Reconstruction disclosed (module docstring). -/
def leveledView (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (r : LeveledSeeds P χ L) :
    LeveledView P L :=
  (fun d => (Regev.keygen P.lwe χ (r.1 d)).1,
    levelKey P (fun d => (Regev.keygen P.lwe χ (r.1 d)).1)
      (fun d => (Regev.keygen P.lwe χ (r.1 d)).2) r.2.1,
    encrypt P (Regev.keygen P.lwe χ (r.1 0)).1 μ r.2.2)

/-- `leveledView P χ L μ r` is `(pk, levelKey P pk s r.2.1, encrypt P (pk 0) μ r.2.2)` with
`(pk d, s d) = Regev.keygen P.lwe χ (r.1 d)`. -/
theorem leveledView_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool)
    (r : LeveledSeeds P χ L) :
    leveledView P χ L μ r =
      (fun d => (Regev.keygen P.lwe χ (r.1 d)).1,
        levelKey P (fun d => (Regev.keygen P.lwe χ (r.1 d)).1)
          (fun d => (Regev.keygen P.lwe χ (r.1 d)).2) r.2.1,
        encrypt P (Regev.keygen P.lwe χ (r.1 0)).1 μ r.2.2) := rfl

/-- **The level hybrid** `H_h`: as `leveledView`, except that every level key `e` with `h ≤ e`
holds encryptions of `0` under `pk_{e+1}` (same coins) instead of the key bits of `s_e`.
`H_L` is the real view (`h = L` replaces nothing) and `H_0` replaces every level key.
`levelHybrid P χ L μ h r = (pk, fun e j => if h ≤ e then encrypt P (pk e.succ) false (r.2.1 e j)
else levelKey P pk s r.2.1 e j, encrypt P (pk 0) μ r.2.2)`. Glue for the top-down hybrid;
reconstruction disclosed (module docstring). -/
def levelHybrid (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (h : ℕ)
    (r : LeveledSeeds P χ L) : LeveledView P L :=
  (fun d => (Regev.keygen P.lwe χ (r.1 d)).1,
    fun e j => if h ≤ e.val then encrypt P (Regev.keygen P.lwe χ (r.1 e.succ)).1 false (r.2.1 e j)
      else levelKey P (fun d => (Regev.keygen P.lwe χ (r.1 d)).1)
        (fun d => (Regev.keygen P.lwe χ (r.1 d)).2) r.2.1 e j,
    encrypt P (Regev.keygen P.lwe χ (r.1 0)).1 μ r.2.2)

/-- `levelHybrid P χ L μ h r` is `(pk, fun e j => if h ≤ e then encrypt P (pk e.succ) false
(r.2.1 e j) else levelKey P pk s r.2.1 e j, encrypt P (pk 0) μ r.2.2)`. -/
theorem levelHybrid_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (h : ℕ)
    (r : LeveledSeeds P χ L) :
    levelHybrid P χ L μ h r =
      (fun d => (Regev.keygen P.lwe χ (r.1 d)).1,
        fun e j => if h ≤ e.val then
            encrypt P (Regev.keygen P.lwe χ (r.1 e.succ)).1 false (r.2.1 e j)
          else levelKey P (fun d => (Regev.keygen P.lwe χ (r.1 d)).1)
            (fun d => (Regev.keygen P.lwe χ (r.1 d)).2) r.2.1 e j,
        encrypt P (Regev.keygen P.lwe χ (r.1 0)).1 μ r.2.2) := rfl

/-- The messages of step `e`: the `N` key bits of `s_e`, indexed by `Fin (N − 1 + 1)` (the
index shape of `hybridPlant`; `N ≥ 1`),
`levelMsgs P χ L e r i = keyBits P (Regev.keygen P.lwe χ (r.1 e.castSucc)).2 (Fin.cast _ i)`.
Glue. -/
def levelMsgs (P : Parameters) (χ : LWE.Noise) (L : ℕ) (e : Fin L) (r : LeveledSeeds P χ L)
    (i : Fin (P.columns - 1 + 1)) : Bool :=
  keyBits P (Regev.keygen P.lwe χ (r.1 e.castSucc)).2
    (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)) i)

/-- `levelMsgs P χ L e r i` is
`keyBits P (Regev.keygen P.lwe χ (r.1 e.castSucc)).2 (Fin.cast _ i)`. -/
theorem levelMsgs_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (e : Fin L)
    (r : LeveledSeeds P χ L) (i : Fin (P.columns - 1 + 1)) :
    levelMsgs P χ L e r i =
      keyBits P (Regev.keygen P.lwe χ (r.1 e.castSucc)).2
        (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)) i) := rfl

/-- The view assembled by the step-`e` reduction around a planted key `v.1` (as `pk_{e+1}`) and
`N` planted ciphertexts `v.2` (as the level key `e`), from its own seeds `c.1` and running `D`
with the coins `c.2`: the other public keys from `c.1`, the level keys `e' > e` as encryptions of
`0` (the hybrid `H_{e+1}`), the level keys `e' < e` honest, and the challenge `Enc_{pk_0}(μ)`.
`levelAssemble P χ L μ e D v c = D (update pk e.succ v.1, fun e' j => if e' = e then
v.2 (Fin.cast _ j) else if e < e' then encrypt P (pk e'.succ) false (c.1.2.1 e' j) else
levelKey P pk s c.1.2.1 e' j, encrypt P (pk 0) μ c.1.2.2) c.2`. Glue. -/
def levelAssemble (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L) {ρ : Type*}
    (D : LeveledView P L → ρ → Bool)
    (v : PublicKey P × (Fin (P.columns - 1 + 1) → Ciphertext P)) (c : LeveledSeeds P χ L × ρ) :
    Bool :=
  D (Function.update (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1) e.succ v.1,
    fun e' j => if e' = e then v.2 (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
      else if e.val < e'.val then
        encrypt P (Regev.keygen P.lwe χ (c.1.1 e'.succ)).1 false (c.1.2.1 e' j)
      else levelKey P (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1)
        (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).2) c.1.2.1 e' j,
    encrypt P (Regev.keygen P.lwe χ (c.1.1 0)).1 μ c.1.2.2) c.2

/-- `levelAssemble P χ L μ e D v c` runs `D` with the coins `c.2` on the view with `pk_{e+1}`
planted as `v.1`, the level key `e` planted as `v.2`, the keys above `e` encrypting `0`, those
below honest, and the challenge `Enc_{pk_0}(μ)` (the formula of `levelAssemble`'s docstring). -/
theorem levelAssemble_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    {ρ : Type*} (D : LeveledView P L → ρ → Bool)
    (v : PublicKey P × (Fin (P.columns - 1 + 1) → Ciphertext P)) (c : LeveledSeeds P χ L × ρ) :
    levelAssemble P χ L μ e D v c =
      D (Function.update (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1) e.succ v.1,
        fun e' j => if e' = e then
            v.2 (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
          else if e.val < e'.val then
            encrypt P (Regev.keygen P.lwe χ (c.1.1 e'.succ)).1 false (c.1.2.1 e' j)
          else levelKey P (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1)
            (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).2) c.1.2.1 e' j,
        encrypt P (Regev.keygen P.lwe χ (c.1.1 0)).1 μ c.1.2.2) c.2 := rfl

/-- **The reduction of step `e` at position `j`** (side `b`): the DLWE test that, on a challenge
key `pk` and its coins `c = (R₀, Rs, r, ρ)`, plants `pk` as `pk_{e+1}`, encrypts under it the
messages of step `e` (the key bits of `s_e`, from its own seeds `r`) at the positions after `j`
and `0` at the positions before `j`, encrypts at position `j` the bit `b ∧ (bit j of s_e)` with
the coins `R₀`, assembles the rest of the view itself (`levelAssemble`) and runs `D`. It is
`hybridPlant` (`EnsembleSecurity.lean`) composed with phase 5's `reduction`:
`levelReduction P χ L μ e j b D pk c = reduction P (if b then levelMsgs P χ L e c.2.2.1 j' else
false) (hybridPlant (encrypt P) (levelMsgs P χ L e c.2.2.1) (fun _ => false) j'
(levelAssemble P χ L μ e D)) pk c`, with `j' = Fin.cast _ j` [GSW13, §3.2, Lemma 1, p009-b002,
p010-b001; AP14, §5.3, p015-b002]. Reconstruction disclosed (module docstring). -/
def levelReduction (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) (b : Bool) {ρ : Type*} (D : LeveledView P L → ρ → Bool)
    (pk : PublicKey P)
    (c : Coins P × ((Fin (P.columns - 1 + 1) → Coins P) × (LeveledSeeds P χ L × ρ))) : Bool :=
  reduction P
    (if b then
      levelMsgs P χ L e c.2.2.1 (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
    else false)
    (hybridPlant (encrypt P) (levelMsgs P χ L e c.2.2.1) (fun _ => false)
      (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j) (levelAssemble P χ L μ e D))
    pk c

/-- `levelReduction P χ L μ e j b D pk c` is `reduction P (if b then levelMsgs P χ L e c.2.2.1 j'
else false) (hybridPlant (encrypt P) (levelMsgs P χ L e c.2.2.1) (fun _ => false) j'
(levelAssemble P χ L μ e D)) pk c` with `j' = Fin.cast _ j`. -/
theorem levelReduction_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) (b : Bool) {ρ : Type*} (D : LeveledView P L → ρ → Bool)
    (pk : PublicKey P)
    (c : Coins P × ((Fin (P.columns - 1 + 1) → Coins P) × (LeveledSeeds P χ L × ρ))) :
    levelReduction P χ L μ e j b D pk c =
      reduction P
        (if b then
          levelMsgs P χ L e c.2.2.1 (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
        else false)
        (hybridPlant (encrypt P) (levelMsgs P χ L e c.2.2.1)
          (fun _ => false) (Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j)
          (levelAssemble P χ L μ e D))
        pk c := rfl

/-- **The term of step `e` at position `j`**: the two DLWE advantages of its reduction (sides
`true` and `false`) plus `2·(N·ε_LHL)`, `ε_LHL = Regev.extractionError P.lwe`, the shape of
`distAdv_encrypt_le`'s right-hand side,
`levelTerm P χ L μ e j D = decisionAdvantage P.lwe χ (levelReduction P χ L μ e j true D) +
decisionAdvantage P.lwe χ (levelReduction P χ L μ e j false D) +
2 * (P.columns * Regev.extractionError P.lwe)` [GSW13, §3.2, Lemma 1, p009-b002, p010-b001].
Glue. -/
noncomputable def levelTerm (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    ℝ :=
  LWE.decisionAdvantage P.lwe χ (levelReduction P χ L μ e j true D) +
    LWE.decisionAdvantage P.lwe χ (levelReduction P χ L μ e j false D) +
    2 * (P.columns * Regev.extractionError P.lwe)

/-- `levelTerm P χ L μ e j D` is the sum of the two DLWE advantages of `levelReduction` (sides
`true`, `false`) and `2 * (P.columns * Regev.extractionError P.lwe)`. -/
theorem levelTerm_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    (j : Fin P.columns) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    levelTerm P χ L μ e j D =
      LWE.decisionAdvantage P.lwe χ (levelReduction P χ L μ e j true D) +
        LWE.decisionAdvantage P.lwe χ (levelReduction P χ L μ e j false D) +
        2 * (P.columns * Regev.extractionError P.lwe) := rfl

/-- The distinguisher of the final step: on a phase-5 view `v = (pk, ct)` and coins `c`, it
plants `pk` as `pk_0` and `ct` as the challenge in the hybrid `H_0` (every level key an
encryption of `0`) built from its own seeds `c.1`, and runs `D` with `c.2`,
`challengeDist P χ L D v c = D (update pk 0 v.1, fun e j => encrypt P (pk e.succ) false
(c.1.2.1 e j), v.2) c.2`. Glue. -/
def challengeDist (P : Parameters) (χ : LWE.Noise) (L : ℕ) {ρ : Type*}
    (D : LeveledView P L → ρ → Bool) (v : PublicKey P × Ciphertext P)
    (c : LeveledSeeds P χ L × ρ) : Bool :=
  D (Function.update (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1) 0 v.1,
    fun e j => encrypt P (Regev.keygen P.lwe χ (c.1.1 e.succ)).1 false (c.1.2.1 e j), v.2) c.2

/-- `challengeDist P χ L D v c` is `D (update pk 0 v.1, fun e j => encrypt P (pk e.succ) false
(c.1.2.1 e j), v.2) c.2`. -/
theorem challengeDist_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) {ρ : Type*}
    (D : LeveledView P L → ρ → Bool) (v : PublicKey P × Ciphertext P)
    (c : LeveledSeeds P χ L × ρ) :
    challengeDist P χ L D v c =
      D (Function.update (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1) 0 v.1,
        fun e j => encrypt P (Regev.keygen P.lwe χ (c.1.1 e.succ)).1 false (c.1.2.1 e j), v.2)
        c.2 := rfl

/-- **The term of the challenge step**: phase 5's bound for the challenge under `pk_0` with the
distinguisher `challengeDist`, `challengeTerm P χ L μ₀ μ₁ D =
decisionAdvantage P.lwe χ (reduction P μ₀ (challengeDist P χ L D)) +
decisionAdvantage P.lwe χ (reduction P μ₁ (challengeDist P χ L D)) +
2 * (P.columns * Regev.extractionError P.lwe)` [GSW13, §3.2, p009-b002]. Glue. -/
noncomputable def challengeTerm (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ₀ μ₁ : Bool)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) : ℝ :=
  LWE.decisionAdvantage P.lwe χ (reduction P μ₀ (challengeDist P χ L D)) +
    LWE.decisionAdvantage P.lwe χ (reduction P μ₁ (challengeDist P χ L D)) +
    2 * (P.columns * Regev.extractionError P.lwe)

/-- `challengeTerm P χ L μ₀ μ₁ D` is the two DLWE advantages of `reduction P μᵢ
(challengeDist P χ L D)` plus `2 * (P.columns * Regev.extractionError P.lwe)`. -/
theorem challengeTerm_eq (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ₀ μ₁ : Bool) {ρ : Type*}
    [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    challengeTerm P χ L μ₀ μ₁ D =
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ (challengeDist P χ L D)) +
        LWE.decisionAdvantage P.lwe χ (reduction P μ₁ (challengeDist P χ L D)) +
        2 * (P.columns * Regev.extractionError P.lwe) := rfl

/-- The position hybrid `G_t` of step `e` (glue for L4): `H_{e+1}` with the first `t` ciphertexts
of the level key `e` replaced by encryptions of `0` under `pk_{e+1}` (same coins),
`levelPosHybrid P χ L μ e t r = (H.1, fun e' i => if e' = e ∧ i < t then
encrypt P (pk e.succ) false (r.2.1 e i) else H.2.1 e' i, H.2.2)` with
`H = levelHybrid P χ L μ (e + 1) r`. -/
private def levelPosHybrid (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L) (t : ℕ)
    (r : LeveledSeeds P χ L) : LeveledView P L :=
  ((levelHybrid P χ L μ (e.val + 1) r).1,
    fun e' i => if e' = e ∧ i.val < t then
        encrypt P (Regev.keygen P.lwe χ (r.1 e.succ)).1 false (r.2.1 e i)
      else (levelHybrid P χ L μ (e.val + 1) r).2.1 e' i,
    (levelHybrid P χ L μ (e.val + 1) r).2.2)

/-- `G_0` is `H_{e+1}`: no position is replaced. -/
private theorem levelPosHybrid_zero (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool)
    (e : Fin L) : levelPosHybrid P χ L μ e 0 = levelHybrid P χ L μ (e.val + 1) := by
  funext r
  simp only [levelPosHybrid, Nat.not_lt_zero, and_false, if_false]

/-- `G_N` is `H_e`: every position of the level key `e` is replaced, and for `e' ≠ e` the
conditions `e + 1 ≤ e'` and `e ≤ e'` agree (`levelHybrid_eq`). -/
private theorem levelPosHybrid_columns (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool)
    (e : Fin L) : levelPosHybrid P χ L μ e P.columns = levelHybrid P χ L μ e.val := by
  funext r
  simp only [levelPosHybrid, levelHybrid_eq, Fin.is_lt, and_true]
  refine Prod.ext rfl (Prod.ext (funext fun e' => funext fun i => ?_) rfl)
  by_cases he : e' = e
  · subst he
    simp
  · have hv : e.val ≠ e'.val := fun h => he (Fin.ext h).symm
    have hle : (e.val + 1 ≤ e'.val) ↔ (e.val ≤ e'.val) := by omega
    simp only [he, if_false, hle]

/-- **On a real key the reduction runs a position hybrid.** On an LWE sample,
`levelReduction P χ L μ e j b D` accepts exactly as `D` accepts `G_j` (`b = true`: position `j`
encrypts its key bit) or `G_{j+1}` (`b = false`: it encrypts `0`).

**Proof sketch.** The bijection `Ψ` of the seeds plants the LWE seed as the key seed of
`pk_{e+1}` and the reduction's coins as the coins of the level key `e` (`R₀` at position `j`, the
others elsewhere), keeping the replaced coordinates as a second factor; `uprob_comp_equiv` and
`uprob_fst` reduce to an identity of the views, read through `levelReduction_eq`, `reduction_eq`,
`view_eq`, `hybridPlant_eq`, `levelAssemble_eq`, `levelMsgs_eq`, `levelHybrid_eq`,
`levelKey_eq`, `evalKey_eq` and `Regev.keygen_fst`. The secret of `pk_{e+1}` is not read (in
`H_{e+1}` the level key `e + 1` encrypts `0`), and the cases `i < j`, `i = j`, `j < i` match the
planted tuple. -/
private theorem acceptProb_sample_levelReduction (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool)
    (e : Fin L) (j : Fin P.columns) (b : Bool) {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (D : LeveledView P L → ρ → Bool) :
    acceptProb (LWE.sample P.lwe χ) (levelReduction P χ L μ e j b D) =
      acceptProb (levelPosHybrid P χ L μ e (if b then j.val else j.val + 1)) D := by
  have h : P.columns - 1 + 1 = P.columns := Nat.sub_one_add_one (NeZero.ne P.columns)
  let Ψ : KeySeed P χ × (Coins P × ((Fin (P.columns - 1 + 1) → Coins P) ×
      (LeveledSeeds P χ L × ρ))) ≃
      (LeveledSeeds P χ L × ρ) × (KeySeed P χ × ((Fin P.columns → Coins P) × Coins P)) :=
    { toFun := fun w => (((Function.update w.2.2.2.1.1 e.succ w.1,
          Function.update w.2.2.2.1.2.1 e
            (Function.update (fun i => w.2.2.1 (Fin.cast h.symm i)) j w.2.1),
          w.2.2.2.1.2.2), w.2.2.2.2),
        (w.2.2.2.1.1 e.succ, w.2.2.2.1.2.1 e, w.2.2.1 (Fin.cast h.symm j)))
      invFun := fun v => (v.1.1.1 e.succ, (v.1.1.2.1 e j,
        (Function.update (fun i => v.1.1.2.1 e (Fin.cast h i)) (Fin.cast h.symm j) v.2.2.2,
          ((Function.update v.1.1.1 e.succ v.2.1, Function.update v.1.1.2.1 e v.2.2.1,
            v.1.1.2.2), v.1.2))))
      left_inv := by
        rintro ⟨k, R₀, Rs, ⟨K, RC, R₁⟩, c⟩
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
        refine Prod.ext rfl (Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl))
        by_cases hi : i = Fin.cast h.symm j
        · subst hi
          simp
        · have hi' : Fin.cast h i ≠ j := fun hc => hi (by rw [← hc]; rfl)
          simp [Function.update_of_ne hi, Function.update_of_ne hi']
      right_inv := by
        rintro ⟨⟨⟨K, RC, R₁⟩, c⟩, ⟨k, rc, r₀⟩⟩
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
        refine Prod.ext (Prod.ext (Prod.ext rfl (Prod.ext ?_ rfl)) rfl)
          (Prod.ext rfl (Prod.ext rfl ?_))
        · funext e' i
          by_cases he : e' = e
          · subst he
            by_cases hi : i = j
            · subst hi
              simp
            · have hi' : Fin.cast h.symm i ≠ Fin.cast h.symm j := fun hc => hi (by
                simpa using congrArg (Fin.cast h) hc)
              simp [Function.update_of_ne hi, Function.update_of_ne hi']
          · simp [Function.update_of_ne he]
        · simp }
  rw [acceptProb_def, acceptProb_def,
    ← uprob_fst (β := KeySeed P χ × ((Fin P.columns → Coins P) × Coins P))
      (fun z : LeveledSeeds P χ L × ρ =>
        D (levelPosHybrid P χ L μ e (if b then j.val else j.val + 1) z.1) z.2 = true),
    ← uprob_comp_equiv Ψ]
  refine congrArg uprob (funext fun w => ?_)
  obtain ⟨k, R₀, Rs, ⟨K, RC, R₁⟩, c⟩ := w
  congr 1
  rw [levelReduction_eq, reduction_eq, view_eq, hybridPlant_eq, levelAssemble_eq]
  simp only [Ψ, Equiv.coe_fn_mk, levelPosHybrid, levelHybrid_eq, levelMsgs_eq, Regev.keygen_fst]
  congr 1
  have hne : e.castSucc ≠ e.succ := (Fin.castSucc_lt_succ e).ne
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext d
    by_cases hd : d = e.succ
    · subst hd
      simp
    · simp [Function.update_of_ne hd]
  · funext e' i
    by_cases he : e' = e
    · subst he
      simp only [true_and, if_true, levelKey_eq, evalKey_eq, Function.update_self,
        Function.update_of_ne hne, lt_self_iff_false, if_false, add_le_iff_nonpos_right,
        Nat.one_ne_zero, nonpos_iff_eq_zero]
      rcases lt_trichotomy i j with hij | rfl | hij
      · have hb : i.val < if b = true then j.val else j.val + 1 := by
          cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
        have hij' : i ≠ j := hij.ne
        simp [Fin.lt_def, hij, hb, Function.update_of_ne hij']
      · cases b <;> simp
      · have hb : ¬ i.val < if b = true then j.val else j.val + 1 := by
          cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
        have hij' : i ≠ j := hij.ne'
        have hlt : ¬ i.val < j.val := by omega
        have hv : i.val ≠ j.val := by omega
        simp [Fin.lt_def, Fin.ext_iff, hlt, hb, hij', hv]
    · have hs : e'.succ ≠ e.succ := fun hs => he (Fin.succ_injective _ hs)
      simp only [he, if_false, false_and, Function.update_of_ne he, Function.update_of_ne hs]
      by_cases hlt : e.val < e'.val
      · have hle : e.val + 1 ≤ e'.val := hlt
        simp only [hlt, hle, if_true]
      · have hle : ¬ e.val + 1 ≤ e'.val := hlt
        have hc : e'.castSucc ≠ e.succ := fun hc => hlt (by
          have := congrArg Fin.val hc
          simp only [Fin.coe_castSucc, Fin.val_succ] at this
          omega)
        simp only [hlt, hle, if_false, levelKey_eq, evalKey_eq,
          Function.update_of_ne hs, Function.update_of_ne hc, Function.update_of_ne he]
  · simp [Function.update_of_ne (Fin.succ_ne_zero e).symm]

/-- **Under a uniform key the two sides are `2·(N·ε_LHL)`-close**: the acceptance probabilities of
`levelReduction P χ L μ e j b D` on a uniform key, `b = true` and `b = false`, differ by at most
`2 * (P.columns * Regev.extractionError P.lwe)`.

**Proof sketch.** Regrouping the seeds (`uprob_comp_equiv`, `uprob_prod`), each side is the average
over the reduction's own seeds `ω` of the acceptance of `uniformKeyView P m` by one test `T ω`
(`levelReduction_eq`, `reduction_eq`, `uniformKeyView_eq`), the bit `m` being the key bit
(`b = true`) or `0`. For each `ω`, `uniformKey_uniform_advantage_le` twice and the triangle
inequality through the uniform view bound the gap by `2·(N·ε_LHL)`; `abs_uexp_sub_le` averages. -/
private theorem abs_acceptProb_id_levelReduction_sub_le (P : Parameters) (χ : LWE.Noise) (L : ℕ)
    (μ : Bool) (e : Fin L) (j : Fin P.columns) {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (D : LeveledView P L → ρ → Bool) :
    |acceptProb (id : PublicKey P → PublicKey P) (levelReduction P χ L μ e j true D) -
        acceptProb (id : PublicKey P → PublicKey P) (levelReduction P χ L μ e j false D)| ≤
      2 * (P.columns * Regev.extractionError P.lwe) := by
  let j' := Fin.cast (Nat.sub_one_add_one (NeZero.ne P.columns)).symm j
  let T : LeveledSeeds P χ L → PublicKey P × Ciphertext P →
      (Fin (P.columns - 1 + 1) → Coins P) × ρ → Bool := fun ω v c =>
    hybridPlant (encrypt P) (levelMsgs P χ L e ω) (fun _ => false) j' (levelAssemble P χ L μ e D)
      v (c.1, (ω, c.2))
  let msg : Bool → LeveledSeeds P χ L → Bool := fun b ω =>
    if b then levelMsgs P χ L e ω j' else false
  have hsec : ∀ b, acceptProb (id : PublicKey P → PublicKey P) (levelReduction P χ L μ e j b D) =
      uexp fun ω => acceptProb (uniformKeyView P (msg b ω)) (T ω) := by
    intro b
    let Φ : PublicKey P × (Coins P × ((Fin (P.columns - 1 + 1) → Coins P) ×
          (LeveledSeeds P χ L × ρ))) ≃
        LeveledSeeds P χ L ×
          ((PublicKey P × Coins P) × ((Fin (P.columns - 1 + 1) → Coins P) × ρ)) :=
      { toFun := fun w => (w.2.2.2.1, ((w.1, w.2.1), (w.2.2.1, w.2.2.2.2)))
        invFun := fun v => (v.2.1.1, (v.2.1.2, (v.2.2.1, (v.1, v.2.2.2))))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [acceptProb_def, ← uprob_comp_equiv Φ.symm, uprob_prod]
    refine congrArg uexp (funext fun ω => ?_)
    rw [acceptProb_def]
    refine congrArg uprob (funext fun z => ?_)
    rw [uniformKeyView_eq, levelReduction_eq, reduction_eq]
    rfl
  have hc : 0 ≤ 2 * (P.columns * Regev.extractionError P.lwe) := by
    have h0 := uniformKey_uniform_advantage_le P false (fun _ (_ : Unit) => true)
    rw [distAdv_def] at h0
    linarith [abs_nonneg (acceptProb (uniformKeyView P false) (fun _ (_ : Unit) => true) -
      acceptProb (id : PublicKey P × Ciphertext P → PublicKey P × Ciphertext P)
        (fun _ (_ : Unit) => true))]
  rw [hsec true, hsec false]
  refine abs_uexp_sub_le hc fun ω => ?_
  have h₁ := uniformKey_uniform_advantage_le P (msg true ω) (T ω)
  have h₂ := uniformKey_uniform_advantage_le P (msg false ω) (T ω)
  rw [distAdv_def] at h₁ h₂
  have htri := abs_sub_le (acceptProb (uniformKeyView P (msg true ω)) (T ω))
    (acceptProb (id : PublicKey P × Ciphertext P → PublicKey P × Ciphertext P) (T ω))
    (acceptProb (uniformKeyView P (msg false ω)) (T ω))
  rw [abs_sub_comm
    (acceptProb (id : PublicKey P × Ciphertext P → PublicKey P × Ciphertext P) (T ω))] at htri
  linarith

/-- The leveled view is the hybrid `H_L`: `leveledView P χ L μ = levelHybrid P χ L μ L`, since no
`e : Fin L` has `L ≤ e` (`leveledView_eq`, `levelHybrid_eq`). -/
private theorem leveledView_eq_levelHybrid (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) :
    leveledView P χ L μ = levelHybrid P χ L μ L := by
  funext r
  rw [leveledView_eq, levelHybrid_eq]
  refine Prod.ext rfl (Prod.ext (funext fun e => funext fun i => ?_) rfl)
  simp only [not_le.mpr e.isLt, if_false]

/-- **The hybrid `H_0` is phase 5's view under `challengeDist`**: `D` accepts `H_0(μ)` exactly as
`challengeDist P χ L D` accepts `realView P χ μ`,
`acceptProb (levelHybrid P χ L μ 0) D = acceptProb (realView P χ μ) (challengeDist P χ L D)`.

**Proof sketch.** `challengeDist_eq` writes the distinguisher as `D` after a map `F` reading its
own seeds, so `acceptProb_bind` moves those seeds into the sampler. The bijection `Ψ` plants the
key seed and the challenge coins of `realView` as those of `pk_0` and of the challenge, keeping the
replaced coordinates as a second factor; through `realView_eq`, `view_eq`, `levelHybrid_eq` and
`Regev.keygen_fst` the sampler is `H_0` of the first factor (in `H_0` every level key encrypts `0`,
so the secrets are not read), and `acceptProb_comp_equiv` and `acceptProb_fst` drop the second. -/
private theorem acceptProb_levelHybrid_zero_realView (P : Parameters) (χ : LWE.Noise) (L : ℕ)
    (μ : Bool) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    acceptProb (levelHybrid P χ L μ 0) D = acceptProb (realView P χ μ) (challengeDist P χ L D) := by
  let Ψ : (KeySeed P χ × Coins P) × LeveledSeeds P χ L ≃
      LeveledSeeds P χ L × (KeySeed P χ × Coins P) :=
    { toFun := fun w => ((Function.update w.2.1 0 w.1.1, w.2.2.1, w.1.2), (w.2.1 0, w.2.2.2))
      invFun := fun v => ((v.1.1 0, v.1.2.2), (Function.update v.1.1 0 v.2.1, v.1.2.1, v.2.2))
      left_inv := by
        rintro ⟨⟨k, R₀⟩, K, RC, R₁⟩
        simp
      right_inv := by
        rintro ⟨⟨K, RC, R₀⟩, k, R₁⟩
        simp }
  let F : PublicKey P × Ciphertext P → LeveledSeeds P χ L → LeveledView P L := fun v ω =>
    (Function.update (fun d => (Regev.keygen P.lwe χ (ω.1 d)).1) 0 v.1,
      fun e j => encrypt P (Regev.keygen P.lwe χ (ω.1 e.succ)).1 false (ω.2.1 e j), v.2)
  have hdist : challengeDist P χ L D = fun v (c : LeveledSeeds P χ L × ρ) => D (F v c.1) c.2 := by
    funext v c
    exact challengeDist_eq P χ L D v c
  have hview : (fun s : (KeySeed P χ × Coins P) × LeveledSeeds P χ L =>
      F (realView P χ μ s.1) s.2) = fun s => levelHybrid P χ L μ 0 (Ψ s).1 := by
    funext s
    obtain ⟨⟨k, R₀⟩, K, RC, R₁⟩ := s
    rw [realView_eq, view_eq]
    simp only [F, Ψ, Equiv.coe_fn_mk, levelHybrid_eq, Regev.keygen_fst, Nat.zero_le, if_true]
    have h0 : ∀ d : Fin (L + 1),
        Function.update (fun d => LWE.sample P.lwe χ (K d)) 0 (LWE.sample P.lwe χ k) d =
          LWE.sample P.lwe χ (Function.update K 0 k d) := by
      intro d
      by_cases hd : d = 0
      · subst hd
        simp
      · simp [Function.update_of_ne hd]
    simp only [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _)]
    rw [← funext h0]
  rw [hdist, acceptProb_bind, hview,
    acceptProb_comp_equiv Ψ (fun z => levelHybrid P χ L μ 0 z.1) D, acceptProb_fst]

/-! ### Targets L4–L5 -/

/-- **L4. One level of the key hybrid.** For every level `e : Fin L`, bit `μ` and distinguisher
`D`, replacing the `N` encryptions under `pk_{e+1}` of the key bits of `s_e` by encryptions of
`0` (from `H_{e+1}` to `H_e`) costs at most the sum of the position terms,
`distAdv (levelHybrid P χ L μ (e + 1)) (levelHybrid P χ L μ e) D ≤
∑ j : Fin P.columns, levelTerm P χ L μ e j D` [AP14, §5.3, p015-b002 (independent keys);
GSW13, §3.2, Lemma 1, p009-b002, p010-b001]. Legitimate because `s_{e+1}` occurs only in the
level key `e + 1`, already replaced in `H_{e+1}` (top-down order). Reconstruction disclosed
(module docstring).

**Proof sketch.** Position hybrids `G_t` (`t ≤ N`, the private `levelPosHybrid`): `H_{e+1}`
with the first `t` ciphertexts of the level key `e` encrypting `0`, so `G_0 = H_{e+1}` and
`G_N = H_e` (`levelHybrid_eq`). `abs_sub_le_sum_hybrids` and `Fin.sum_univ_eq_sum_range` reduce to
the gaps `|Pr[D(G_j)] − Pr[D(G_{j+1})]|`, as in the proof of `distAdv_multi_le_sum` (whose
`hybridPlant` the reduction uses); the lemma itself does not apply, the messages (the bits of
`s_e`) being drawn inside the reduction's coins (r3 §H8 item 12), so its proof is followed with
them in the coins. On a real LWE key, `levelReduction P χ L μ e j b D` accepts exactly as `D`
accepts `G_j` (`b = true`) or `G_{j+1}` (`b = false`): a bijection of the seeds plants the LWE
seed as the key seed of `pk_{e+1}`, whose secret `H_{e+1}` does not read, and the reduction's
coins as those of the level key `e` (`uprob_comp_equiv`, `uprob_fst`; `levelReduction_eq`,
`reduction_eq`, `view_eq`, `hybridPlant_eq`, `levelAssemble_eq`, `levelMsgs_eq`, `levelHybrid_eq`,
`Regev.keygen_fst`). So by the triangle inequality the gap is at most the two DLWE advantages
(`LWE.decisionAdvantage_eq`, `distAdv_def`) plus the gap between `b = true` and `b = false` under
a uniform key, which is the average over the reduction's own seeds (`uprob_prod`) of the gap of
`uniformKeyView` at two bits for one test, at most `2·(N·ε_LHL)` for each value of the seeds
(`uniformKey_uniform_advantage_le`, twice) and so on average (`abs_uexp_sub_le`). Sum over `j`
(`levelTerm_eq`). -/
theorem distAdv_levelHybrid_le (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    distAdv (levelHybrid P χ L μ (e.val + 1)) (levelHybrid P χ L μ e.val) D ≤
      ∑ j : Fin P.columns, levelTerm P χ L μ e j D := by
  -- The position hybrids: `G t` is the acceptance of `levelPosHybrid P χ L μ e t`.
  let G : ℕ → ℝ := fun t => acceptProb (levelPosHybrid P χ L μ e t) D
  -- One position: two exact DLWE advantages and the uniform-key gap.
  have hstep : ∀ j : Fin P.columns, |G j - G (j + 1)| ≤ levelTerm P χ L μ e j D := by
    intro j
    have ht := acceptProb_sample_levelReduction P χ L μ e j true D
    have hf := acceptProb_sample_levelReduction P χ L μ e j false D
    simp only [if_true, Bool.false_eq_true, if_false] at ht hf
    have hu := abs_acceptProb_id_levelReduction_sub_le P χ L μ e j D
    rw [levelTerm_eq, LWE.decisionAdvantage_eq, LWE.decisionAdvantage_eq, distAdv_def,
      distAdv_def]
    show |acceptProb (levelPosHybrid P χ L μ e j) D -
      acceptProb (levelPosHybrid P χ L μ e (j + 1)) D| ≤ _
    rw [← ht, ← hf]
    have h₁ := abs_sub_le (acceptProb (LWE.sample P.lwe χ) (levelReduction P χ L μ e j true D))
      (acceptProb (id : PublicKey P → PublicKey P) (levelReduction P χ L μ e j true D))
      (acceptProb (LWE.sample P.lwe χ) (levelReduction P χ L μ e j false D))
    have h₂ := abs_sub_le
      (acceptProb (id : PublicKey P → PublicKey P) (levelReduction P χ L μ e j true D))
      (acceptProb (id : PublicKey P → PublicKey P) (levelReduction P χ L μ e j false D))
      (acceptProb (LWE.sample P.lwe χ) (levelReduction P χ L μ e j false D))
    rw [abs_sub_comm
      (acceptProb (id : PublicKey P → PublicKey P) (levelReduction P χ L μ e j false D))] at h₂
    linarith
  -- The telescoping chain `G 0 = H_{e+1}`, …, `G N = H_e`.
  calc distAdv (levelHybrid P χ L μ (e.val + 1)) (levelHybrid P χ L μ e.val) D
      = |G 0 - G P.columns| := by
        rw [distAdv_def, ← levelPosHybrid_zero P χ L μ e, ← levelPosHybrid_columns P χ L μ e]
    _ ≤ ∑ t ∈ Finset.range P.columns, |G t - G (t + 1)| := abs_sub_le_sum_hybrids G P.columns
    _ = ∑ j : Fin P.columns, |G j - G (j + 1)| :=
        (Fin.sum_univ_eq_sum_range (fun t => |G t - G (t + 1)|) P.columns).symm
    _ ≤ ∑ j : Fin P.columns, levelTerm P χ L μ e j D := Finset.sum_le_sum fun j _ => hstep j

/-- **L5. IND-CPA of leveled GSW-FHE from DLWE.** For all bits `μ₀`, `μ₁` and every
distinguisher `D`, the leveled views of `μ₀` and `μ₁` differ by at most the sum of the level
terms of both hybrid chains plus the challenge term,
`distAdv (leveledView P χ L μ₀) (leveledView P χ L μ₁) D ≤
∑ e : Fin L, ∑ j : Fin P.columns, (levelTerm P χ L μ₀ e j D + levelTerm P χ L μ₁ e j D) +
challengeTerm P χ L μ₀ μ₁ D` [BV14, Thm 2.14 first part, p008-b003, and Thm 3.7, p016-b001;
BV11, Thm 3.1, p015-b001]. No circular-security assumption. Deviation: r3's `2·∑ levelTerm`
becomes the sum over the two chains, the level terms depending on the challenge bit;
reconstruction disclosed (module docstring).

**Proof sketch.** `leveledView P χ L μ = levelHybrid P χ L μ L` (`leveledView_eq`,
`levelHybrid_eq`: no `e : Fin L` has `L ≤ e`; the private `leveledView_eq_levelHybrid`). On each
side, `abs_sub_le_sum_hybrids` over `H_0(μ), …, H_L(μ)` (`Fin.sum_univ_eq_sum_range`) and L4
(`distAdv_levelHybrid_le`) at every level bound `|Pr[D(H_0(μ))] − Pr[D(H_L(μ))]|` by
`∑ e, ∑ j, levelTerm P χ L μ e j D`. The middle step: `D` accepts `H_0(μ)` exactly as
`challengeDist P χ L D` accepts phase 5's `realView P χ μ` (the private
`acceptProb_levelHybrid_zero_realView`: `challengeDist_eq` and `acceptProb_bind` move its seeds into
the sampler; a seed bijection plants the key seed and the challenge coins of `realView` as those of
`pk_0` and of the challenge, `realView_eq`, `view_eq`, `levelHybrid_eq`, `Regev.keygen_fst`;
`acceptProb_comp_equiv` and `acceptProb_fst` drop the replaced coordinates), so phase 5's
`distAdv_encrypt_le` bounds it by `challengeTerm P χ L μ₀ μ₁ D` (`challengeTerm_eq`). The triangle
inequality (`abs_sub_le`), `Finset.sum_add_distrib` and `linarith` conclude. -/
theorem distAdv_leveledView_le (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ₀ μ₁ : Bool)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    distAdv (leveledView P χ L μ₀) (leveledView P χ L μ₁) D ≤
      ∑ e : Fin L, ∑ j : Fin P.columns,
          (levelTerm P χ L μ₀ e j D + levelTerm P χ L μ₁ e j D) +
        challengeTerm P χ L μ₀ μ₁ D := by
  -- Each chain `H_0(μ), …, H_L(μ)`: L4 at every level.
  have hchain : ∀ μ : Bool, |acceptProb (levelHybrid P χ L μ 0) D -
      acceptProb (levelHybrid P χ L μ L) D| ≤ ∑ e : Fin L, ∑ j : Fin P.columns,
        levelTerm P χ L μ e j D := by
    intro μ
    calc |acceptProb (levelHybrid P χ L μ 0) D - acceptProb (levelHybrid P χ L μ L) D|
        ≤ ∑ t ∈ Finset.range L, |acceptProb (levelHybrid P χ L μ t) D -
            acceptProb (levelHybrid P χ L μ (t + 1)) D| :=
          abs_sub_le_sum_hybrids (fun t => acceptProb (levelHybrid P χ L μ t) D) L
      _ = ∑ e : Fin L, |acceptProb (levelHybrid P χ L μ e.val) D -
            acceptProb (levelHybrid P χ L μ (e.val + 1)) D| :=
          (Fin.sum_univ_eq_sum_range (fun t => |acceptProb (levelHybrid P χ L μ t) D -
            acceptProb (levelHybrid P χ L μ (t + 1)) D|) L).symm
      _ ≤ ∑ e : Fin L, ∑ j : Fin P.columns, levelTerm P χ L μ e j D :=
          Finset.sum_le_sum fun e _ => by
            rw [abs_sub_comm, ← distAdv_def]
            exact distAdv_levelHybrid_le P χ L μ e D
  -- The middle step: phase 5's bound on `challengeDist`.
  have hmid := distAdv_encrypt_le P χ μ₀ μ₁ (challengeDist P χ L D)
  rw [← challengeTerm_eq, distAdv_def, ← acceptProb_levelHybrid_zero_realView,
    ← acceptProb_levelHybrid_zero_realView] at hmid
  have h₀ := hchain μ₀
  have h₁ := hchain μ₁
  rw [distAdv_def, leveledView_eq_levelHybrid, leveledView_eq_levelHybrid]
  simp only [Finset.sum_add_distrib]
  have htri₀ := abs_sub_le (acceptProb (levelHybrid P χ L μ₀ L) D)
    (acceptProb (levelHybrid P χ L μ₀ 0) D) (acceptProb (levelHybrid P χ L μ₁ L) D)
  have htri₁ := abs_sub_le (acceptProb (levelHybrid P χ L μ₀ 0) D)
    (acceptProb (levelHybrid P χ L μ₁ 0) D) (acceptProb (levelHybrid P χ L μ₁ L) D)
  have hcomm := abs_sub_comm (acceptProb (levelHybrid P χ L μ₀ L) D)
    (acceptProb (levelHybrid P χ L μ₀ 0) D)
  linarith

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

set_option pp.fullNames true
set_option pp.funBinderTypes true
#check @TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.distAdv_levelHybrid_le
#check @TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.distAdv_leveledView_le
