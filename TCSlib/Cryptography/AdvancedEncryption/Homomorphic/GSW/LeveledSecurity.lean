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

Both are admitted statement-phase targets.

**Sources and reconstruction (P6-Q19 B).** The key-chain construction and the hybrid order are
reconstructed: no ingested passage gives them. BV11 and BV14 attribute leveled bootstrapping
to Gentry's work; that passage will be cited here once it is ingested. The statements cite
[BV11, Thm 3.1, Def 3.6], [BV14, Thm 2.14 first part, Thm 3.7] and [AP14, §5.3] only, with
[GSW13, §3.2, Lemma 1], [BV11, Def 3.1] and [BV14, §2.5] for the one-key steps and the view.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Thm 2.14 (first part), Thm 3.7.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.1, Def 3.6, Thm 3.1.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: §5.3.
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; IACR ePrint 2013/340, version dated
  8 June 2013: §3.2, Lemma 1.

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

/-! ### Targets L4–L5 -/

/-- **L4. One level of the key hybrid.** For every level `e : Fin L`, bit `μ` and distinguisher
`D`, replacing the `N` encryptions under `pk_{e+1}` of the key bits of `s_e` by encryptions of
`0` (from `H_{e+1}` to `H_e`) costs at most the sum of the position terms,
`distAdv (levelHybrid P χ L μ (e + 1)) (levelHybrid P χ L μ e) D ≤
∑ j : Fin P.columns, levelTerm P χ L μ e j D` [AP14, §5.3, p015-b002 (independent keys);
GSW13, §3.2, Lemma 1, p009-b002, p010-b001]. Legitimate because `s_{e+1}` occurs only in the
level key `e + 1`, already replaced in `H_{e+1}` (top-down order). Reconstruction disclosed
(module docstring).

**Proof sketch.** Position hybrids `G_i` (`i ≤ N`) between `H_{e+1}` (`G_0`) and `H_e` (`G_N`):
the first `i` ciphertexts of the level key `e` encrypt `0`. `abs_sub_le_sum_hybrids` reduces
to the gaps `|Pr[D(G_i)] − Pr[D(G_{i+1})]|`, as in `distAdv_multi_le_sum` (whose
`hybridPlant` the reduction uses; the messages, the bits of `s_e`, are drawn inside the
reduction's coins, r3 §H8 item 12, so the multi-ciphertext lemma is applied per value of the
other seeds or its proof is followed with them in the coins). The gap at `i = j` is the gap of
`levelReduction P χ L μ e j b D` between a real LWE key and a uniform key, plus the gap
between `b = true` and `b = false` under a uniform key: `levelReduction_eq`, `reduction_eq`,
`hybridPlant_eq` (the planted position), `levelAssemble_eq`, `levelHybrid_eq`, `Regev.keygen_fst`
(the planted key is distributed as `pk_{e+1}`, whose secret is otherwise unused in `H_{e+1}`),
and the seed regrouping (`acceptProb_comp_equiv`, `OneWay.uprob_update`). As in phase 5's
`distAdv_encrypt_le`: the two DLWE gaps are the exact advantages (`real_uniformKey_advantage`,
`LWE.decisionAdvantage_eq`), and the uniform-key gap is at most `2·(N·ε_LHL)` for each value
of the reduction's own seeds (`uniformKey_uniform_advantage_le`, twice), averaged. Sum over
`j` (`levelTerm_eq`). -/
theorem distAdv_levelHybrid_le (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    distAdv (levelHybrid P χ L μ (e.val + 1)) (levelHybrid P χ L μ e.val) D ≤
      ∑ j : Fin P.columns, levelTerm P χ L μ e j D := by
  sorry

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
`levelHybrid_eq`: no `e : Fin L` has `L ≤ e`). The chain `H_L(μ₀), …, H_0(μ₀), H_0(μ₁), …,
H_L(μ₁)`: `abs_sub_le_sum_hybrids` (or the triangle inequality, `abs_sub_le`) on each side
with L4 (`distAdv_levelHybrid_le`) for `e = L − 1, …, 0` (`Fin.sum_univ_eq_sum_range`). The
middle step: `H_0(μ)` is `challengeDist P χ L D` run on phase 5's `realView P χ μ`, after the
seed regrouping (`challengeDist_eq`, `realView_eq`, `view_eq`, `Regev.keygen_fst`, and
`acceptProb_comp_equiv`; the seed of `pk_0` and the unused coordinates are integrated out), so
phase 5's `distAdv_encrypt_le` bounds it by `challengeTerm P χ L μ₀ μ₁ D` (`challengeTerm_eq`).
`linarith`. -/
theorem distAdv_leveledView_le (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ₀ μ₁ : Bool)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    distAdv (leveledView P χ L μ₀) (leveledView P χ L μ₁) D ≤
      ∑ e : Fin L, ∑ j : Fin P.columns,
          (levelTerm P χ L μ₀ e j D + levelTerm P χ L μ₁ e j D) +
        challengeTerm P χ L μ₀ μ₁ D := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
