/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Basic
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Experiments
import Mathlib.Data.Fin.Tuple.Basic
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "sub_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Scheme_A_strict"
  let includeEval := false
  let projectionCoes := false
  let rec parts : Lean.Name → List (String × String)
    | .anonymous => []
    | .str p s => parts p ++ [("str", s)]
    | .num p n => parts p ++ [("num", toString n)]
  let rec isProjectionBody (e : Lean.Expr) : Bool :=
    match e.consumeMData with
    | .lam _ _ body _ => isProjectionBody body
    | value => match value.getAppFn with
      | .const n _ => env.isProjectionFn n
      | _ => false
  let rec stripLambdas (e : Lean.Expr) : Lean.Expr :=
    match e.consumeMData with
    | .lam _ _ body _ => stripLambdas body
    | value => value
  let mut requested : Array Lean.Name := #[]
  let mut excluded : Nat := 0
  for (name, ci) in env.constants.toList.toArray.qsort (fun a b => Lean.Name.lt a.1 b.1) do
    let some idx := env.getModuleIdxFor? name | continue
    let home := env.header.moduleNames[idx.toNat]!
    unless home.getRoot == `TCSlib && ci.isDefinition do continue
    let status := Lean.getReducibilityStatusCore env name
    let matcher := Lean.Meta.isMatcherCore env name
    let instanceFlag := Lean.Meta.isInstanceCore env name
    let coeProjection := match ci with
      | .defnInfo d =>
        let value := stripLambdas d.value
        match value.getAppFn with
        | .const n _ =>
          (n == `CoeFun.mk || n == `Coe.mk) &&
            value.getAppArgs.back?.any isProjectionBody
        | _ => false
      | _ => false
    let eligible := (status != .reducible || matcher) &&
      (includeEval || name != `Complexity.PolyExpr.eval) &&
      !(projectionCoes && instanceFlag && coeProjection)
    let row := Lean.Json.mkObj [
      ("name", Lean.toJson name.toString), ("components", Lean.toJson (parts name)),
      ("home", Lean.toJson home.toString), ("home_components", Lean.toJson (parts home)),
      ("status", Lean.toJson status.toAttrString), ("matcher", Lean.toJson matcher),
      ("instance", Lean.toJson instanceFlag), ("projection_coercion", Lean.toJson coeProjection),
      ("eligible", Lean.toJson eligible)]
    Lean.logInfo m!"GSWCORE-CATALOG {label} {row.compress}"
    if eligible then requested := requested.push name else excluded := excluded + 1
  let mut active : Nat := 0
  let mut already : Nat := 0
  for name in requested do
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    if before == .irreducible then already := already + 1
    else
      let id := Lean.mkIdent name
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
      active := active + 1
    let installed ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus name
    unless installed == .irreducible do throwError "GSWCORE seal installation failed: {name}"
  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do throwError "GSWCORE seal requires base scope"
  let mut scopedNames : Std.HashSet Lean.Name := {}
  for (_, payloads) in scopes.scopedEntries.map.toList do
    for name in payloads do scopedNames := scopedNames.insert name
  let entryFields (entry : Lean.Meta.InstanceEntry) :=
    (entry.keys, Lean.ExprStructEq.mk entry.val, entry.priority, entry.globalName?,
      entry.synthOrder, entry.attrKind)
  let lookupSnapshot (environment : Lean.Environment) :=
    let state := Lean.Meta.instanceExtension.getState environment
    (state.discrTree.toArray.map (fun (keys, entry) => (keys, entryFields entry)),
      state.instanceNames.toArray.map (fun (name, entry) => (name, entryFields entry)),
      state.erased.toList)
  let beforeLookup := lookupSnapshot env
  for name in requested do
    if scopedNames.contains name then throwError "GSWCORE scoped instance overlap: {name}"
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      requested.foldl (fun state name => state.erase name) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "GSWCORE typeclass lookup changed"
  for name in requested do
    if Lean.Meta.isGlobalInstance maskedEnv name then
      throwError "GSWCORE instance unfolding mask failed: {name}"
  Lean.logInfo m!"GSWCORE-INSTALL {label} requested={requested.size} active={active} already={already} excluded={excluded} tc_state=preserved"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key GSW: key generation, encryption, decryption and fresh-noise correctness

## Main definitions

* Key generation is the existing Regev key generation `Regev.keygen P.lwe χ`; GSW adds no
  key material.
* `secretVector`: the key vector `t = (−s, 1)`, with `tᵗ Ā = eᵗ` for the augmented public key.
* `encrypt`: `C = Ā R + μ G`, with `Ā` the existing `Regev.augmented` public key and
  `R ∈ {0,1}^{m×N}`.
* `halfVector`, `decryptColumn`, `decrypt`: decrypt by the existing Regev decryptor applied
  to the column `C · G⁻¹(⌊q/2⌋ e_{n+1})`.

## Main results

* `vecMul_secretVector_augmented`: `tᵗ Ā = eᵗ` [Pei16, Equation (6.1.7)].
* `encrypts_encrypt`: a fresh encryption has noise at most `m·B`.
* `decrypt_of_encrypts`: noise `β` with `2·(ℓ·β) < ⌊q/2⌋` decrypts correctly.
* `decrypt_of_encrypts_dyadic`: at `q = 2^ℓ` the factor `ℓ` disappears.
* `decrypt_keygen_encrypt`: every-coin correctness of the basic scheme.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.1 (`SecretKeyGen`, `PublicKeyGen`, `Enc`, `Dec`).
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 6.1.3 (Equation (6.1.7), "Fully homomorphic encryption").
* [AP14] J. Alperin-Sheriff, C. Peikert, ePrint 2014/094 version dated 13 June 2014,
  Section 3.2 (`GSW.Dec`) and Claim 3.4.
* [BV14] Z. Brakerski, V. Vaikuntanathan, ePrint 2013/541, Section 3.1 (`NCCrypt.PubEnc`,
  `NCCrypt.Dec`) and Lemma 3.2.

**Deviations.** (1) Gadget form: `C = ĀR + μG` [Pei16, Section 6.1.3, with the sign of `R`
flipped] instead of [GSW13]'s `Flatten(μ·I_N + BitDecomp(R·A))`; [GSW13, Section 3.2] notes
`BitDecomp⁻¹(C) = μG + RA`, so the two carry the same information. (2) Rows are samples in the
LWE layer, so `Ā` is the transpose-plus-value-row `Regev.augmented`, and `t = (−s, 1)` puts
the `1` last (GSW13 puts it first). (3) Decryption: [GSW13] reads the row with `vᵢ = 2^i ∈
(q/4, q/2]`, [AP14] the penultimate column (`2^{ℓ−2} ∈ [q/4, q/2)`), both with error `< q/8`
and a custom rounding. Here the column `C · G⁻¹(⌊q/2⌋ e_{n+1})` is a Regev ciphertext of the
message, so the audited `Regev.decrypt` and its strict nearest-codepoint rule are reused for
every `q ≥ 2`; the price is a factor `≤ ℓ` in the decryption noise, which disappears for
`q = 2^ℓ`. (4) Noise is a finite-seed bounded law, so correctness holds for every coin, not
with overwhelming probability [BV14, Lemma 3.3]. The secret is uniform, as in the LWE layer.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- The GSW key vector `t = (−s, 1) ∈ Z_q^{n+1}` [GSW13, Section 3.1, `SecretKeyGen`, with the
`1` moved last; Pei16, Section 6.1.3, `s = (−s̄, 1)`]. -/
def secretVector (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) :
    Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus :=
  Fin.snoc (α := fun _ => ZMod P.lwe.modulus) (-s) 1

/-- `secretVector P s` is `−s` followed by `1`. -/
theorem secretVector_eq (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) :
    secretVector P s = Fin.snoc (α := fun _ => ZMod P.lwe.modulus) (-s) 1 := rfl

/-- `tᵗ Ā = eᵗ`: the key vector annihilates the augmented LWE public key up to the row errors
[Pei16, Equation (6.1.7); GSW13, Section 3.1, "Observe that `A · s = e`"].

**Proof sketch.** Write coordinate `i` of `tᵗ Ā` as a sum over the `n+1` rows and split off the
last row (`Fin.sum_univ_castSucc`). Column `i` of `Regev.augmented` is the `i`-th sample's row
followed by its value (`Regev.augmented_eq`, `Fin.snoc_castSucc`, `Fin.snoc_last`), and `t` is
`−s` followed by `1`. The inner product is `−⟨s, aᵢ⟩ + (⟨aᵢ, s⟩ + eᵢ)` by
`LWE.noisyValues_apply`; commuting the factors of `⟨s, aᵢ⟩` cancels it, leaving `eᵢ`. -/
theorem vecMul_secretVector_augmented (P : Parameters)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) :
    Matrix.vecMul (secretVector P s) (Regev.augmented P.lwe (A, LWE.noisyValues P.lwe A s e)) =
      fun i => (e i : ZMod P.lwe.modulus) := by
  funext i
  -- Step 1: the product at column `i` as a sum, with the last row split off.
  change ∑ j, secretVector P s j *
      Regev.augmented P.lwe (A, LWE.noisyValues P.lwe A s e) j i = _
  rw [Fin.sum_univ_castSucc, secretVector_eq, Regev.augmented_eq]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Matrix.transpose_apply, Pi.neg_apply,
    LWE.noisyValues_apply, one_mul, neg_mul, Finset.sum_neg_distrib]
  -- Step 2: `−⟨s, aᵢ⟩ + (⟨aᵢ, s⟩ + eᵢ) = eᵢ`.
  have hc : ∑ j, s j * A i j = ∑ j, A i j * s j :=
    Finset.sum_congr rfl fun j _ => mul_comm (s j) (A i j)
  rw [hc, neg_add_cancel_left]

/-- Public-key GSW encryption `C = Ā R + μ G` with `R ∈ {0,1}^{m×N}` [Pei16, Section 6.1.3,
"An encryption of an integer `x` is a matrix `A = xG − ĀR`", sign of `R` flipped; GSW13,
Section 3.1, `Enc`, gadget form]. The public key is a Regev/LWE public key `(A, b)`. -/
def encrypt (P : Parameters)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Bool) (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) : Ciphertext P :=
  Regev.augmented P.lwe pk * lift P R + (μ.toNat : ZMod P.lwe.modulus) • gadget P

/-- `encrypt P pk μ R` is the augmented public key times the lifted `R`, plus `μ` times `G`. -/
theorem encrypt_eq (P : Parameters)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Bool) (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    encrypt P pk μ R =
      Regev.augmented P.lwe pk * lift P R + (μ.toNat : ZMod P.lwe.modulus) • gadget P := rfl

/-- The target `w = ⌊q/2⌋ · e_{n+1}`: zero in the first `n` coordinates and the Regev bit
codepoint for `true` in the last. Technical decryption glue. -/
def halfVector (P : Parameters) : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus :=
  Fin.snoc (α := fun _ => ZMod P.lwe.modulus) 0 (LWE.BitEncoding.codepoint P.lwe true)

/-- `halfVector P` is `0` followed by `codepoint true = ⌊q/2⌋`. -/
theorem halfVector_eq (P : Parameters) :
    halfVector P =
      Fin.snoc (α := fun _ => ZMod P.lwe.modulus) 0 (LWE.BitEncoding.codepoint P.lwe true) := rfl

/-- The decryption column `C · G⁻¹(w)`. For a valid encryption of `μ` it is a Regev
ciphertext of `μ` in augmented form [GSW13, Section 3.1, "Dec is a BitDecomp'd version of
Regev's decryption procedure"; AP14, Section 3.2, `GSW.Dec`, generalized column]. -/
def decryptColumn (P : Parameters) (C : Ciphertext P) :
    Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus :=
  C.mulVec (fun i => ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus))

/-- `decryptColumn P C` is `C` applied to the lifted decomposition of `halfVector P`. -/
theorem decryptColumn_eq (P : Parameters) (C : Ciphertext P) :
    decryptColumn P C =
      C.mulVec (fun i => ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus)) := rfl

/-- GSW decryption: split the decryption column into its first `n` coordinates and its last
coordinate, and apply the existing Regev decryptor [GSW13, Section 3.1, `Dec`; BV14,
Section 3.1, `NCCrypt.Dec`, "standard Regev decryption"]. -/
def decrypt (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C : Ciphertext P) : Bool :=
  Regev.decrypt P.lwe s (Fin.init (decryptColumn P C), decryptColumn P C (Fin.last _))

/-- `decrypt P s C` is Regev decryption of the split decryption column. -/
theorem decrypt_eq (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C : Ciphertext P) :
    decrypt P s C =
      Regev.decrypt P.lwe s (Fin.init (decryptColumn P C), decryptColumn P C (Fin.last _)) :=
  rfl

/-- **Fresh-encryption noise.** With row errors bounded by `B`, a public-key encryption of `μ`
encrypts `μ` under `t = (−s,1)` with noise at most `m·B` [GSW13, Section 3.1, "The error
`⟨Rᵢ, e⟩` has magnitude at most `‖e‖₁`"; Pei16, Section 6.1.3].

**Proof sketch.** The witness is `j ↦ ∑ᵢ eᵢ · R i j`, bounded by `m·B` through
`LWE.binaryErrorSum_bound` applied to column `j` of `R`. `Matrix.vecMul_add`,
`Matrix.vecMul_smul` and `Matrix.vecMul_vecMul` give `tᵗ C = (tᵗ Ā) R + μ tᵗ G`, and
`vecMul_secretVector_augmented` replaces `tᵗ Ā` by `eᵗ`. Coordinate `j` of `eᵗ R` is
`∑ᵢ eᵢ · R i j` read modulo `q` (`lift_apply`, `Int.cast_sum`, `Int.cast_mul`). -/
theorem encrypts_encrypt (P : Parameters)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (μ : Bool)
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    Encrypts P (secretVector P s) (μ.toNat : ℤ) (P.lwe.samples * B)
      (encrypt P (A, LWE.noisyValues P.lwe A s e) μ R) := by
  rw [encrypts_iff]
  refine ⟨fun j => ∑ i, e i * ((R i j).toNat : ℤ),
    fun j => LWE.binaryErrorSum_bound e (fun i => R i j) B he, ?_⟩
  -- Step 1: `tᵗ C = (tᵗ Ā) R + μ tᵗ G`, and `tᵗ Ā = eᵗ`.
  rw [encrypt_eq, Matrix.vecMul_add, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul,
    vecMul_secretVector_augmented, Int.cast_natCast, add_comm]
  -- Step 2: `eᵗ R` is the cast of the integer subset sums.
  congr 1
  funext j
  change ∑ i, (e i : ZMod P.lwe.modulus) * lift P R i j = _
  simp only [lift_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

/-- Fresh-encryption noise for the actual key generator and a `B`-bounded noise law.

**Proof sketch.** `Regev.keygen_fst` and `Regev.keygen_snd` expose the sample and the secret;
`LWE.sample_fst` and `LWE.sample_snd` write the sample as `(A, A s + e)` with
`eᵢ = χ.sample(seedᵢ)`, and `Noise.bounded_iff` bounds each `eᵢ` by `B`. Then apply
`encrypts_encrypt`. -/
theorem encrypts_keygen_encrypt (P : Parameters) (χ : LWE.Noise)
    (rg : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins)))
    (B : ℕ) (hχ : χ.Bounded B) (μ : Bool)
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    Encrypts P (secretVector P (Regev.keygen P.lwe χ rg).2) (μ.toNat : ℤ) (P.lwe.samples * B)
      (encrypt P (Regev.keygen P.lwe χ rg).1 μ R) := by
  have hs : LWE.sample P.lwe χ rg =
      (rg.1, LWE.noisyValues P.lwe rg.1 rg.2.1 (fun i => χ.sample (rg.2.2 i))) :=
    Prod.ext (LWE.sample_fst P.lwe χ rg) (LWE.sample_snd P.lwe χ rg)
  rw [Regev.keygen_fst, Regev.keygen_snd, hs]
  exact encrypts_encrypt P rg.1 rg.2.1 _ B
    (fun i => (LWE.Noise.bounded_iff χ B).1 hχ (rg.2.2 i)) μ R

/-- `halfVector P` vanishes at every coordinate except the last. Technical glue. -/
private theorem halfVector_eq_zero_of_ne_last (P : Parameters) (j : Fin (P.lwe.dimension + 1))
    (hj : j ≠ Fin.last P.lwe.dimension) : halfVector P j = 0 := by
  obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.2 hj
  rw [halfVector_eq, Fin.snoc_castSucc, Pi.zero_apply]

/-- If `C` encrypts the bit `b` under `t = (−s,1)` with the error vector `e`, decryption decodes
`codepoint b` plus the integer error sum of `e` against the decomposition of `halfVector P`.
Technical glue shared by the two decryption theorems.

**Proof sketch.** The Regev residual of the split column `v = C x` is `⟨t, v⟩`, by splitting
off the last coordinate. Then `⟨t, C x⟩ = ⟨tᵗ C, x⟩`, the invariant gives
`b·⟨tᵗ G, x⟩ + ⟨e, x⟩ = b·⟨t, G x⟩ + ⟨e, x⟩`, `G x = w` and `⟨t, w⟩ = codepoint true`. -/
private theorem decrypt_eq_decode_errorSum (P : Parameters)
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (b : Bool) (β : ℕ) (C : Ciphertext P)
    (h : Encrypts P (secretVector P s) (b.toNat : ℤ) β C) :
    ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ β) ∧
      decrypt P s C = LWE.BitEncoding.decode P.lwe (LWE.BitEncoding.codepoint P.lwe b +
        ((∑ i, e i * ((decomposeVec P (halfVector P) i).toNat : ℤ) : ℤ) :
          ZMod P.lwe.modulus)) := by
  obtain ⟨e, he, hC⟩ := (encrypts_iff P _ _ β C).1 h
  refine ⟨e, he, ?_⟩
  -- Step 1: the Regev residual of the split column `v = C x` is `⟨t, v⟩`.
  have hsplit : decryptColumn P C (Fin.last _) - ∑ j, s j * Fin.init (decryptColumn P C) j =
      dotProduct (secretVector P s) (C.mulVec
        (fun i => ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus))) := by
    rw [← decryptColumn_eq]
    change _ = ∑ i, secretVector P s i * decryptColumn P C i
    rw [Fin.sum_univ_castSucc, secretVector_eq]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.neg_apply, neg_mul, one_mul,
      Finset.sum_neg_distrib, Fin.init_def]
    abel
  -- Step 2: `⟨t, w⟩ = codepoint true`, and `b · codepoint true = codepoint b`.
  have hw : dotProduct (secretVector P s) (halfVector P) =
      LWE.BitEncoding.codepoint P.lwe true := by
    change ∑ i, secretVector P s i * halfVector P i = _
    rw [Fin.sum_univ_castSucc, secretVector_eq, halfVector_eq]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add, one_mul]
  have hb : ((b.toNat : ℤ) : ZMod P.lwe.modulus) * LWE.BitEncoding.codepoint P.lwe true =
      LWE.BitEncoding.codepoint P.lwe b := by
    cases b <;> simp only [LWE.BitEncoding.codepoint_eq, Bool.toNat_false, Bool.toNat_true,
      Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one, zero_mul, one_mul,
      Bool.false_eq_true, if_false, if_true]
  -- Step 3: the error term is the cast of the integer error sum.
  have herr : dotProduct (fun j => (e j : ZMod P.lwe.modulus))
      (fun i => ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus)) =
      ((∑ i, e i * ((decomposeVec P (halfVector P) i).toNat : ℤ) : ℤ) :
        ZMod P.lwe.modulus) := by
    change ∑ i, (e i : ZMod P.lwe.modulus) *
      ((decomposeVec P (halfVector P) i).toNat : ZMod P.lwe.modulus) = _
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  -- Step 4: assemble `⟨t, C x⟩ = b·⟨t, G x⟩ + ⟨e, x⟩`.
  rw [decrypt_eq, Regev.decrypt_eq]
  dsimp only
  rw [hsplit, Matrix.dotProduct_mulVec, hC, add_dotProduct, smul_dotProduct,
    ← Matrix.dotProduct_mulVec, gadget_mulVec_decomposeVec, hw, herr, smul_eq_mul, hb]

/-- **Decryption from the invariant.** If `C` encrypts the bit `b` under `t = (−s,1)` with
noise `β` and `2·(ℓ·β) < ⌊q/2⌋`, then `decrypt P s C = b` [GSW13, Section 3.1, "if
`xᵢ = μ·vᵢ + e'` for some error `e'` of magnitude at most `q/8` … Dec … output[s] the correct
value"; AP14, Claim 3.4; BV14, Lemma 3.2].

**Proof sketch.** The private glue lemma `decrypt_eq_decode_errorSum` does the algebra:
`Regev.decrypt_eq` reads `c.2 − ⟨s, c.1⟩`, which for the split column `v` is `⟨t, v⟩`
(`Fin.sum_univ_castSucc`, `secretVector_eq`). `Matrix.dotProduct_mulVec` turns `⟨t, C x⟩` into
`⟨tᵗC, x⟩` with `x = G⁻¹(w)` lifted; substituting the invariant gives
`b·⟨t, G x⟩ + ⟨e, x⟩ = b·⟨t, w⟩ + ⟨e, x⟩` by `gadget_mulVec_decomposeVec`, and `⟨t, w⟩ = ⌊q/2⌋`
because `w` vanishes off the last coordinate where `t` is `1`. So the residual is
`codepoint b + ⟨e, x⟩`. Since `w` vanishes off the last coordinate,
`errorSum_decomposeVec_le` (with `j₀ = last`) bounds `|⟨e, x⟩| ≤ ℓ·β`, and
`LWE.BitEncoding.decode_codepoint_add` with `B := ℓ·β` finishes. -/
theorem decrypt_of_encrypts (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (b : Bool) (β : ℕ) (C : Ciphertext P) (h : Encrypts P (secretVector P s) (b.toNat : ℤ) β C)
    (hsep : 2 * (P.width * β) < P.lwe.modulus / 2) :
    decrypt P s C = b := by
  obtain ⟨e, he, hdec⟩ := decrypt_eq_decode_errorSum P s b β C h
  rw [hdec]
  exact LWE.BitEncoding.decode_codepoint_add P.lwe (P.width * β) b _
    (errorSum_decomposeVec_le P (halfVector P) (Fin.last _)
      (halfVector_eq_zero_of_ne_last P) e β he) hsep

/-- At a power-of-two modulus `q = 2^ℓ` with `ℓ ≥ 1`, noise `β` with `2β < q/2` decrypts
correctly: `⌊q/2⌋ = 2^{ℓ−1}` has a single binary digit, so the decryption column is the last
gadget column [AP14, Claim 3.4, dyadic case; GSW13, Section 3.1, `MPDec` remark].

**Proof sketch.** As `decrypt_of_encrypts`, the residual is `codepoint b + ⟨e, x⟩` with `x` the
decomposition of `w` (`decrypt_eq_decode_errorSum`). Here `⌊q/2⌋ = 2^{ℓ−1} < q`, and `x` is the
indicator of the single position `i₀ = (n, ℓ−1)` (last block and top position, zero-based):
both have the same block digits (`Lossy.digits_val`, `digits_decomposeVec`, `digit_val`; the
last block's positional sum is `2^{ℓ−1}`, every other block's is `0 = w_j`), and the digit map
is injective (`Lossy.digits_injective`). So the error sum is the single entry `e i₀`, bounded by
`β`, and `LWE.BitEncoding.decode_codepoint_add` with `B := β` finishes. -/
theorem decrypt_of_encrypts_dyadic (P : Parameters)
    (hq : P.lwe.modulus = 2 ^ P.width) (hℓ : 0 < P.width)
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (b : Bool) (β : ℕ) (C : Ciphertext P)
    (h : Encrypts P (secretVector P s) (b.toNat : ℤ) β C)
    (hsep : 2 * β < P.lwe.modulus / 2) :
    decrypt P s C = b := by
  obtain ⟨e, he, hdec⟩ := decrypt_eq_decode_errorSum P s b β C h
  rw [hdec]
  have hl : P.width - 1 < P.width := Nat.sub_lt hℓ Nat.one_pos
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin P.columns,
      i₀ = finProdFinEquiv (Fin.last P.lwe.dimension, ⟨P.width - 1, hl⟩) := ⟨_, rfl⟩
  -- Step 1: `⌊q/2⌋ = 2^{ℓ-1}`, a residue below `q`.
  have hhalf : P.lwe.modulus / 2 = 2 ^ (P.width - 1) := by
    have h2 : 2 ^ P.width = 2 ^ (P.width - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hℓ]
    rw [hq, h2, Nat.mul_div_cancel _ two_pos]
  have hlt : P.lwe.modulus / 2 < P.lwe.modulus :=
    Nat.div_lt_self (by have := P.lwe.modulus_ge_two; omega) one_lt_two
  -- Step 2: the decomposition of `w` is the indicator of `i₀ = (last, ℓ-1)`, since its digit
  -- vector is that of `w` (`digits_val`) and the digit map is injective.
  have hz : decomposeVec P (halfVector P) = fun i => decide (i = i₀) := by
    apply TrapdoorFunctions.Lossy.digits_injective P.width (P.lwe.dimension + 1)
    rw [digits_decomposeVec]
    funext j
    apply Fin.ext
    simp only [digit_val, TrapdoorFunctions.Lossy.digits_val]
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · rw [halfVector_eq, Fin.snoc_last, LWE.BitEncoding.codepoint_eq, if_pos rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt hlt, hhalf,
        Fintype.sum_eq_single (⟨P.width - 1, hl⟩ : Fin P.width)]
      · rw [← hi₀, decide_eq_true rfl, Bool.toNat_true, one_mul]
      · intro k hk
        have hne : finProdFinEquiv (Fin.last P.lwe.dimension, k) ≠ i₀ := by
          rw [hi₀]
          intro hk'
          exact hk (Prod.ext_iff.1 (finProdFinEquiv.injective hk')).2
        rw [decide_eq_false hne, Bool.toNat_false, zero_mul]
    · rw [halfVector_eq, Fin.snoc_castSucc, Pi.zero_apply, ZMod.val_zero]
      symm
      refine Finset.sum_eq_zero fun k _ => ?_
      have hne : finProdFinEquiv (j'.castSucc, k) ≠ i₀ := by
        rw [hi₀]
        intro hk'
        exact Fin.castSucc_ne_last j' (Prod.ext_iff.1 (finProdFinEquiv.injective hk')).1
      rw [decide_eq_false hne, Bool.toNat_false, zero_mul]
  -- Step 3: the error sum is the single entry `e i₀`, bounded by `β`.
  have hsum : (∑ i, e i * ((decomposeVec P (halfVector P) i).toNat : ℤ)) = e i₀ := by
    rw [hz, Fintype.sum_eq_single i₀]
    · dsimp only
      rw [decide_eq_true rfl, Bool.toNat_true, Nat.cast_one, mul_one]
    · intro i hi
      dsimp only
      rw [decide_eq_false hi, Bool.toNat_false, Nat.cast_zero, mul_zero]
  rw [hsum]
  exact LWE.BitEncoding.decode_codepoint_add P.lwe β b (e i₀) (he i₀) hsep

/-- **Basic correctness.** Every key-generation seed, message and encryption coin matrix
decrypts correctly when the noise law is `B`-bounded and `2·(ℓ·(m·B)) < ⌊q/2⌋` [GSW13,
Section 3.1; BV14, Lemmas 3.2–3.3, worst-case form].

**Proof sketch.** `encrypts_keygen_encrypt`, then `decrypt_of_encrypts`. -/
theorem decrypt_keygen_encrypt (P : Parameters) (χ : LWE.Noise)
    (rg : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins)))
    (B : ℕ) (hχ : χ.Bounded B) (μ : Bool)
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool)
    (hsep : 2 * (P.width * (P.lwe.samples * B)) < P.lwe.modulus / 2) :
    decrypt P (Regev.keygen P.lwe χ rg).2 (encrypt P (Regev.keygen P.lwe χ rg).1 μ R) = μ := by
  exact decrypt_of_encrypts P _ μ (P.lwe.samples * B) _
    (encrypts_keygen_encrypt P χ rg B hχ μ R) hsep

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW


run_cmd do
  let label := "sub_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Scheme_A_strict"
  Lean.logInfo m!"GSWCORE-EOF {label}"
