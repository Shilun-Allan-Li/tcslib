/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Lean
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum
/- DLC-SEAL AdvancedEncryption_Homomorphic_GSW_DecryptFormula: whole-file closure seal of `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/DecryptFormula.lean`, variant A (PolyExpr.eval open), coe (projection coercions open). -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
  let coeOpen : Bool := true
  let coeClasses : List Lean.Name := [`CoeFun, `Coe, `CoeSort, `CoeOut, `CoeTail, `CoeHead,
    `CoeTC, `CoeHTCT, `CoeDep]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  let mut coeExcl : Array Lean.Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    if coeOpen && Lean.Meta.isInstanceCore env n then
      let isCoeCls := match d.type.getForallBody.getAppFn.constName? with
        | some c => coeClasses.contains c
        | none => false
      if isCoeCls then
        let body := dlcStripLam d.value
        let args := body.getAppArgs
        let projArg := match args.back? with
          | some a => match (dlcStripLam a).getAppFn.constName? with
            | some p => (env.getProjectionFnInfo? p).isSome
            | none => false
          | none => false
        if projArg then
          coeExcl := coeExcl.push n
          continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL AdvancedEncryption_Homomorphic_GSW_DecryptFormula: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The GSW decryption formula and the augmented NAND formula

## Main definitions

* `keyBits`: the `N` key bits `G⁻¹(t)` of `t = (−s, 1)`, the bits the evaluation key encrypts.
* `decConstants`: the public constants `Gᵀc` of a ciphertext, `c` its decryption column.
* `decryptFormula`: decryption as a fan-in-2 formula in the key bits, the modular interval sum
  `FormulaArith.modSumInterval` over the constants with the decoding interval of O2.
* `nandFormula`: BV14's augmented decryption function `f_{C₁,C₂}`, `¬(Dec C₁ ∧ Dec C₂)`, one key
  block.
* `decDepth`: the depth bound `FormulaArith.modSumDepth N q` of the decryption formula.
* The instance `Parameters.neZero_columns`: `N = (n+1)·ℓ ≥ 1`, since `2 ≤ q ≤ 2^ℓ`.

## Main results

* `vecMul_secretVector_eq_sum` (G5): `⟨t, c⟩ = ∑ᵢ xᵢ·(Gᵀc)ᵢ` with `x = keyBits`.
* `decryptFormula_eval` (G6), `nandFormula_eval` (G7): the formulas compute decryption and its
  NAND on the key bits.
* `depth_nandFormula_le`, `maxFanin_nandFormula_le`, `decDepth_le` (G8): depth `decDepth + 1`,
  fan-in two, and the closed form `9⌈log₂ N⌉ + 2⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉ + 21`, with no term
  linear in `ℓ`.

All are proved, as are the definitions and the instance.

## References

* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  IACR ePrint 2013/541: Prop 3.4, Def 2.13, Lemma 4.4.
* [BV11] Z. Brakerski, V. Vaikuntanathan, *Efficient Fully Homomorphic Encryption from
  (Standard) LWE*, FOCS 2011 full version; IACR ePrint 2011/344: Def 3.7, Lemma 4.5 with its
  proof. [BV14] cites this lemma as "[BV11, Lemma 4.1]"; it is Lemma 4.5 in the version held.
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; IACR ePrint 2014/094: §5.1.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, §5.4.3 (the gadget `G` and `G⁻¹`).

**Deviations.** Decryption is the library's: the decryption column `c = C·G⁻¹(⌊q/2⌋·e_{n+1})`
decoded by `LWE.BitEncoding.decode`, which is the interval test `decode_iff_mem_Ico` (O2). The
formula is the carry-save modular interval sum of the formula layer (r3 §H3.4; BV11 computes
the bit by subtracting the multiples of `q` and a selection tree), with depth stated by an
explicit constant rather than `O(log N + log log q)`. The augmented formula reads one block of
`N` key bits: the two decryptions share the key, BV14's `f_{c₁,c₂}` literally.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

/-- The ciphertext width `N = (n+1)·ℓ` is positive: `2 ≤ q ≤ 2^ℓ` forces `ℓ ≥ 1`. The
decryption formula has `N` inputs, and Barrington's construction needs at least one. -/
instance Parameters.neZero_columns (P : Parameters) : NeZero P.columns :=
  ⟨Nat.mul_ne_zero (Nat.succ_ne_zero _)
    (Nat.one_lt_two_pow_iff.mp (Nat.lt_of_lt_of_le P.lwe.modulus_ge_two P.modulus_le))⟩

/-- The **key bits** of a secret `s`: the `N = (n+1)·ℓ` bits `G⁻¹(t)` of the key vector
`t = (−s, 1)`, `keyBits P s = decomposeVec P (secretVector P s)`. They are what the
evaluation key encrypts (P6-Q8) [BV11, Def 3.8, p015-b001: encryptions of the bits of the
secret key; AP14, §5.1, p014-b001]. -/
def keyBits (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) :
    Fin P.columns → Bool :=
  decomposeVec P (secretVector P s)

/-- `keyBits P s` is `decomposeVec P (secretVector P s)`. -/
theorem keyBits_eq (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) :
    keyBits P s = decomposeVec P (secretVector P s) := rfl

/-- The **public decryption constants** of a ciphertext `C`: `Gᵀc`, where
`c = decryptColumn P C`, that is `decConstants P C = Matrix.vecMul (decryptColumn P C)
(gadget P)`. Decryption is a binary subset sum of these constants weighted by the key bits
[AP14, §5.1, p014-b001; Pei16, §5.4.3, p052-b001]. -/
def decConstants (P : Parameters) (C : Ciphertext P) : Fin P.columns → ZMod P.lwe.modulus :=
  Matrix.vecMul (decryptColumn P C) (gadget P)

/-- `decConstants P C` is `Matrix.vecMul (decryptColumn P C) (gadget P)`. -/
theorem decConstants_eq (P : Parameters) (C : Ciphertext P) :
    decConstants P C = Matrix.vecMul (decryptColumn P C) (gadget P) := rfl

/-- **The decryption formula** of `C`, on the `N` key bits: the modular interval sum of the
formula layer over the representatives of the public constants, modulo `q`, with the decoding
interval of O2,
`decryptFormula P C = modSumInterval (fun i => (decConstants P C i).val) q (decodeLo P.lwe)
(decodeHi P.lwe)` [BV14, Prop 3.4, p011-b001; BV11, Lemma 4.5, p029-b001]. It tests
`decodeLo ≤ (∑ᵢ xᵢ·aᵢ) mod q < decodeHi`. -/
def decryptFormula (P : Parameters) (C : Ciphertext P) : TreeCircuit P.columns :=
  FormulaArith.modSumInterval (fun i => (decConstants P C i).val) P.lwe.modulus
    (LWE.BitEncoding.decodeLo P.lwe) (LWE.BitEncoding.decodeHi P.lwe)

/-- `decryptFormula P C` is `modSumInterval (fun i => (decConstants P C i).val) q (decodeLo P.lwe)
(decodeHi P.lwe)`. -/
theorem decryptFormula_eq (P : Parameters) (C : Ciphertext P) :
    decryptFormula P C =
      FormulaArith.modSumInterval (fun i => (decConstants P C i).val) P.lwe.modulus
        (LWE.BitEncoding.decodeLo P.lwe) (LWE.BitEncoding.decodeHi P.lwe) := rfl

/-- **The augmented NAND formula** `f_{C₁,C₂}` [BV14, Def 2.13, p008-b002; BV11, Def 3.7,
p014-b002]: the De Morgan negation of the conjunction of the two decryption formulas, on one
block of `N` key bits, `nandFormula P C₁ C₂ = (and2 (decryptFormula P C₁)
(decryptFormula P C₂)).neg`. -/
def nandFormula (P : Parameters) (C₁ C₂ : Ciphertext P) : TreeCircuit P.columns :=
  (TreeCircuit.and2 (decryptFormula P C₁) (decryptFormula P C₂)).neg

/-- `nandFormula P C₁ C₂` is `(and2 (decryptFormula P C₁) (decryptFormula P C₂)).neg`. -/
theorem nandFormula_eq (P : Parameters) (C₁ C₂ : Ciphertext P) :
    nandFormula P C₁ C₂ =
      (TreeCircuit.and2 (decryptFormula P C₁) (decryptFormula P C₂)).neg := rfl

/-- The depth bound of the decryption formula, `decDepth P = modSumDepth N q`, the formula
layer's bound for `N` summands modulo `q` [BV14, Lemma 4.4, p019-b001: the augmented
decryption circuit has depth `c_dec·log(k log(q(k))) + 1`]. -/
def decDepth (P : Parameters) : ℕ :=
  FormulaArith.modSumDepth P.columns P.lwe.modulus

/-- `decDepth P` is `FormulaArith.modSumDepth P.columns P.lwe.modulus`. -/
theorem decDepth_eq (P : Parameters) :
    decDepth P = FormulaArith.modSumDepth P.columns P.lwe.modulus := rfl

/-! ### Targets G5–G8 -/

/-- **G5. Decryption is a binary subset sum of public constants.** For every secret `s` and
ciphertext `C`, the inner product of the key vector `t = (−s, 1)` with the decryption column
`c` is the sum of the public constants `Gᵀc` selected by the key bits:
`secretVector P s ⬝ᵥ decryptColumn P C = ∑ i, ((keyBits P s i).toNat : ZMod q) *
decConstants P C i` [AP14, §5.1, p014-b001; Pei16, §5.4.3, p052-b001, p053-b001].

**Proof sketch.** `keyBits_eq` and `gadget_mulVec_decomposeVec` give `t = G·x` with `x` the
lifted key bits, so `⟨t, c⟩ = ⟨G x, c⟩`. By `Matrix.dotProduct_mulVec` this is
`⟨x, cᵀG⟩ = ⟨x, decConstants P C⟩` (`decConstants_eq`), and `dotProduct` unfolds to the stated
sum (`dotProduct_comm` for the factor order). -/
theorem vecMul_secretVector_eq_sum (P : Parameters)
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (C : Ciphertext P) :
    secretVector P s ⬝ᵥ decryptColumn P C =
      ∑ i, ((keyBits P s i).toNat : ZMod P.lwe.modulus) * decConstants P C i := by
  -- `t = G·x` with `x` the lifted key bits
  have ht : secretVector P s =
      (gadget P).mulVec (fun i => ((keyBits P s i).toNat : ZMod P.lwe.modulus)) := by
    rw [keyBits_eq, gadget_mulVec_decomposeVec]
  rw [ht, dotProduct_comm, Matrix.dotProduct_mulVec, ← decConstants_eq, dotProduct_comm]
  rfl

/-- **G6. The decryption formula computes decryption.** On the key bits of `s`, the
decryption formula of `C` evaluates to GSW decryption of `C` under `s`:
`(decryptFormula P C).eval (keyBits P s) = decrypt P s C` [BV14, Prop 3.4, p011-b001; BV11,
Lemma 4.5, p029-b001, with its proof, p029-b002]. Deviation: the interval-sum construction of
the formula layer (module docstring).

**Proof sketch.** Decryption is `decode` of `⟨t, c⟩` with `t = (−s, 1)`, by the owner-side
reader `decrypt_eq_decode_dotProduct : decrypt P s C = LWE.BitEncoding.decode P.lwe
(secretVector P s ⬝ᵥ decryptColumn P C)` in `GSW/Scheme.lean` (owner-side, ruling Q-C1); the
fill does not re-derive it.
By G5, `⟨t, c⟩` is `∑ᵢ xᵢ·aᵢ` in `ZMod q`. Its representative is `(∑ᵢ xᵢ·aᵢ.val) mod q`
(`ZMod.val_natCast`, `Nat.cast_sum`, `ZMod.natCast_zmod_val`).
`LWE.BitEncoding.decode_iff_mem_Ico` (O2) turns `decode` into the interval test, and
`FormulaArith.modSumInterval_eval` (F9) evaluates the formula to the same test, with
`aᵢ.val < q` (`ZMod.val_lt`) and `decodeLo ≤ decodeHi ≤ q` (`decodeLo_eq`, `decodeHi_eq`,
`omega`). Both sides are Booleans equal as propositions. -/
theorem decryptFormula_eval (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C : Ciphertext P) : (decryptFormula P C).eval (keyBits P s) = decrypt P s C := by
  have hq := P.lwe.modulus_ge_two
  -- the decoding interval lies in `[0, q]`
  have hlh : LWE.BitEncoding.decodeLo P.lwe ≤ LWE.BitEncoding.decodeHi P.lwe := by
    rw [LWE.BitEncoding.decodeLo_eq, LWE.BitEncoding.decodeHi_eq]; omega
  have hhq : LWE.BitEncoding.decodeHi P.lwe ≤ P.lwe.modulus := by
    rw [LWE.BitEncoding.decodeHi_eq]; omega
  -- the representative of `⟨t, c⟩` is the natural subset sum modulo `q` (G5)
  have hval : (secretVector P s ⬝ᵥ decryptColumn P C).val =
      (∑ i, (keyBits P s i).toNat * (decConstants P C i).val) % P.lwe.modulus := by
    have hcast : (∑ i, ((keyBits P s i).toNat : ZMod P.lwe.modulus) * decConstants P C i) =
        ((∑ i, (keyBits P s i).toNat * (decConstants P C i).val : ℕ) : ZMod P.lwe.modulus) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [vecMul_secretVector_eq_sum, hcast, ZMod.val_natCast]
  -- both sides are the interval test (O2 and F9)
  rw [decrypt_eq_decode_dotProduct, decryptFormula_eq,
    FormulaArith.modSumInterval_eval (a := fun i => (decConstants P C i).val)
      (fun i => ZMod.val_lt _) hlh hhq]
  refine Bool.eq_iff_iff.mpr ?_
  rw [decide_eq_true_iff, LWE.BitEncoding.decode_iff_mem_Ico, hval]

/-- **G7. The augmented NAND formula** computes the NAND of the two decryptions under the
same key: `(nandFormula P C₁ C₂).eval (keyBits P s) = !(decrypt P s C₁ && decrypt P s C₂)`
[BV14, Def 2.13, p008-b002; BV11, Def 3.7, p014-b002]. One key block: both decryptions read
the bits of the same `s` (r3 G7).

**Proof sketch.** `nandFormula_eq`, `TreeCircuit.neg_eval` (F1), `TreeCircuit.and2_eval`
(F3), then G6 for each operand. -/
theorem nandFormula_eval (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C₁ C₂ : Ciphertext P) :
    (nandFormula P C₁ C₂).eval (keyBits P s) = !(decrypt P s C₁ && decrypt P s C₂) := by
  rw [nandFormula_eq, TreeCircuit.neg_eval, TreeCircuit.and2_eval, decryptFormula_eval,
    decryptFormula_eval]

/-- **G8, depth.** The augmented NAND formula has depth at most `decDepth P + 1`:
`(nandFormula P C₁ C₂).depth ≤ decDepth P + 1` [BV14, Lemma 4.4, p019-b001: depth
`c_dec·log(k log(q(k))) + 1`].

**Proof sketch.** `nandFormula_eq`, `TreeCircuit.depth_neg` (F1),
`TreeCircuit.depth_and2_le` (F3), and `FormulaArith.depth_modSumInterval_le` (F10) for both
operands, read through `decryptFormula_eq` and `decDepth_eq`; `max_le` and `omega`. -/
theorem depth_nandFormula_le (P : Parameters) (C₁ C₂ : Ciphertext P) :
    (nandFormula P C₁ C₂).depth ≤ decDepth P + 1 := by
  have h₁ := FormulaArith.depth_modSumInterval_le (fun i => (decConstants P C₁ i).val)
    P.lwe.modulus (LWE.BitEncoding.decodeLo P.lwe) (LWE.BitEncoding.decodeHi P.lwe)
  have h₂ := FormulaArith.depth_modSumInterval_le (fun i => (decConstants P C₂ i).val)
    P.lwe.modulus (LWE.BitEncoding.decodeLo P.lwe) (LWE.BitEncoding.decodeHi P.lwe)
  rw [← decryptFormula_eq, ← decDepth_eq] at h₁ h₂
  have h₃ := TreeCircuit.depth_and2_le (decryptFormula P C₁) (decryptFormula P C₂)
  have h₄ := max_le h₁ h₂
  rw [nandFormula_eq, TreeCircuit.depth_neg]
  omega

/-- **G8, fan-in.** The augmented NAND formula has fan-in at most two:
`(nandFormula P C₁ C₂).maxFanin ≤ 2` [BV11, Lemma 4.5, p029-b001: "fan-in 2 gates"].

**Proof sketch.** `nandFormula_eq`, `TreeCircuit.maxFanin_neg` (F1),
`TreeCircuit.maxFanin_and2_le` (F3) and `FormulaArith.maxFanin_modSumInterval_le` (F10) for
both operands (`decryptFormula_eq`); `omega`. -/
theorem maxFanin_nandFormula_le (P : Parameters) (C₁ C₂ : Ciphertext P) :
    (nandFormula P C₁ C₂).maxFanin ≤ 2 := by
  have h₁ := FormulaArith.maxFanin_modSumInterval_le (fun i => (decConstants P C₁ i).val)
    P.lwe.modulus (LWE.BitEncoding.decodeLo P.lwe) (LWE.BitEncoding.decodeHi P.lwe)
  have h₂ := FormulaArith.maxFanin_modSumInterval_le (fun i => (decConstants P C₂ i).val)
    P.lwe.modulus (LWE.BitEncoding.decodeLo P.lwe) (LWE.BitEncoding.decodeHi P.lwe)
  rw [← decryptFormula_eq] at h₁ h₂
  have h₃ := TreeCircuit.maxFanin_and2_le (decryptFormula P C₁) (decryptFormula P C₂)
  rw [nandFormula_eq, TreeCircuit.maxFanin_neg]
  omega

/-- **G8, closed form.** The decryption depth is `O(log N + log log q)` with no term linear in
`ℓ`: `decDepth P ≤ 9 * Nat.clog 2 P.columns + 2 * Nat.clog 2 (P.width + Nat.clog 2 P.columns
+ 3) + 21` [BV14, Lemma 4.4, p019-b001; BV11, Lemma 4.5, p029-b001]. Deviation: an explicit
constant (the *(fix)* of r3 G8, settled here) for BV14's `c_dec`, with `ℓ` for `⌈log₂ q⌉`.

**Proof sketch.** `decDepth_eq`, then `FormulaArith.modSumDepth_le` (F10) for `M = N`; its
inner term `⌈log₂ q⌉ ≤ ℓ` because `q ≤ 2^ℓ` (`P.modulus_le`, `Nat.clog_le_iff_le_pow`), so
`Nat.clog_mono_right` bounds `⌈log₂(⌈log₂ q⌉ + ⌈log₂ N⌉ + 3)⌉` by
`⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉`; `omega`. -/
theorem decDepth_le (P : Parameters) :
    decDepth P ≤
      9 * Nat.clog 2 P.columns + 2 * Nat.clog 2 (P.width + Nat.clog 2 P.columns + 3) + 21 := by
  -- `⌈log₂ q⌉ ≤ ℓ`, since `q ≤ 2^ℓ`
  have hq : Nat.clog 2 P.lwe.modulus ≤ P.width :=
    (Nat.clog_le_iff_le_pow (by norm_num)).mpr P.modulus_le
  have hmono := Nat.clog_mono_right 2
    (show Nat.clog 2 P.lwe.modulus + Nat.clog 2 P.columns + 3 ≤
      P.width + Nat.clog 2 P.columns + 3 by omega)
  have hF := FormulaArith.modSumDepth_le P.columns P.lwe.modulus
  rw [decDepth_eq]
  omega

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
