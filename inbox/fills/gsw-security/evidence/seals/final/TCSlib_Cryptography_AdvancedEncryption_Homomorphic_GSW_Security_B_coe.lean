/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Hashing.SIS.Columns
import TCSlib.Cryptography.LWE.Experiments
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import Mathlib.Tactic.Simps.Basic
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "final_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Security_B_coe"
  let includeEval := true
  let projectionCoes := true
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
    Lean.logInfo m!"GSWSEC-CATALOG {label} {row.compress}"
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
    unless installed == .irreducible do throwError "GSWSEC seal installation failed: {name}"
  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do throwError "GSWSEC seal requires base scope"
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
    if scopedNames.contains name then throwError "GSWSEC scoped instance overlap: {name}"
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      requested.foldl (fun state name => state.erase name) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "GSWSEC typeclass lookup changed"
  for name in requested do
    if Lean.Meta.isGlobalInstance maskedEnv name then
      throwError "GSWSEC instance unfolding mask failed: {name}"
  Lean.logInfo m!"GSWSEC-INSTALL {label} requested={requested.size} active={active} already={already} excluded={excluded} tc_state=preserved"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key GSW: IND-CPA security from decisional LWE (concrete hybrids)

## Main definitions

* `view`, `realView`, `uniformKeyView`: publish the key and one GSW encryption of a fixed bit.
* `reduction`: the DLWE test that encrypts under its challenge key with its own coins.
* `columnHashParameters`: the SIS-hash shape `(n+1) × m` of the augmented public key.

## Main results

* `real_uniformKey_advantage`: real-to-uniform-key advantage equals one DLWE advantage.
* `uniformKey_uniform_advantage_le`: under a uniform key the view is within
  `N · ε_LHL` of uniform, with `ε_LHL = Regev.extractionError`.
* `distAdv_encrypt_le`: two fixed bits' views differ by at most two DLWE advantages plus
  `2·N·ε_LHL` [GSW13, Section 3.2].
* `distAdv_encrypt_le_of_width`: with `(n+1)·w + 2κ ≤ m` the statistical term is at most
  `N · 2^{−κ}`.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.2 and Lemma 1 ("the joint distribution `(A, R·A)` is computationally
  indistinguishable from uniform"; "it suffices to take `m > 2n log q`").
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 6.1.3 ("semantic security follows by a lossiness argument") and
  Section 5.2.1 (Regev's hybrids).
* [BV14] Z. Brakerski, V. Vaikuntanathan, ePrint 2013/541, Section 3.1, "Security".

**Scope.** Concrete, fixed-bit, single-ciphertext statements with function-level
distinguishers, exactly as the audited Regev PKE hybrids. The LWE instance has the GSW
key's `m` rows and one common uniform secret. The asymptotic primitive bridge (`NUPPT`
reductions, `BitPublicKeyScheme.SingleBitSecure`) is a separate unit after the Regev PKE
bridge; multi-ciphertext security then follows from the existing shared-key hybrid
`distAdv_multi_le_sum` (Encryption/PublicKey/EnsembleSecurity.lean:134).
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- The view `(pk, Enc_pk(μ; R))` [GSW13, Section 3.2, passive-view formulation]. -/
@[simps! (config := { isSimp := false }) fst snd]
def view (P : Parameters) (μ : Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P :=
  (pk, encrypt P pk μ R)

/-- The view is the key paired with its GSW encryption. -/
theorem view_eq (P : Parameters) (μ : Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (R : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    view P μ pk R = (pk, encrypt P pk μ R) := rfl

/-- The real view: an actual LWE public key and independent uniform binary `R` [GSW13,
Section 3.1]. -/
@[simps! (config := { isSimp := false }) fst snd]
def realView (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P :=
  view P μ (LWE.sample P.lwe χ r.1) r.2

/-- The real sampler applies `view` to the existing common-secret LWE sample. -/
theorem realView_eq (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    realView P χ μ r = view P μ (LWE.sample P.lwe χ r.1) r.2 := rfl

/-- The first hybrid encrypts under an independent uniform key [GSW13, Section 3.2;
Pei16, Section 6.1.3, "a uniformly random (malformed) public key"]. -/
@[simps! (config := { isSimp := false }) fst snd]
def uniformKeyView (P : Parameters) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P :=
  view P μ r.1 r.2

/-- The uniform-key hybrid applies `view` to its uniform key seed. -/
theorem uniformKeyView_eq (P : Parameters) (μ : Bool)
    (r : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) ×
        Matrix (Fin P.lwe.samples) (Fin P.columns) Bool) :
    uniformKeyView P μ r = view P μ r.1 r.2 := rfl

/-- The DLWE reduction: encrypt the fixed bit under the challenge key with independent
binary coins, then run the view distinguisher with its own coins [GSW13, Section 3.2,
Lemma 1, computational half]. -/
def reduction {ρ : Type*} (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (r : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool × ρ) : Bool :=
  D (view P μ pk r.1) r.2

/-- The reduction calls the distinguisher on exactly one simulated view. -/
theorem reduction_eq {ρ : Type*} (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool)
    (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (r : Matrix (Fin P.lwe.samples) (Fin P.columns) Bool × ρ) :
    reduction P μ D pk r = D (view P μ pk r.1) r.2 := rfl

/-- The SIS-hash shape of the augmented public key: `n+1` rows, `m` binary columns, modulus
`q`. The norm budget is unused by the unconditional extraction argument. Technical glue.

**Disclosure.** Field-for-field equal to `Regev.hashParameters`; a GSW-local copy because
GSW's types index matrices by `Fin (n+1)`, and reading `Regev.hashParameters` at the type level
would unfold another file's definition (Rule 10). Alternative: Regev publishes a domain
equivalence. Either needs a maintainer decision. -/
def columnHashParameters (P : Parameters) : TCSlib.Cryptography.SIS.Parameters where
  dimension := P.lwe.dimension + 1
  columns := P.lwe.samples
  modulus := P.lwe.modulus
  sqNormBound := P.lwe.samples
  modulus_ge_two := P.lwe.modulus_ge_two

attribute [simps (config := { isSimp := false }) dimension columns modulus sqNormBound]
  columnHashParameters

/-- **Computational hybrid.** The real view and the uniform-key view are distinguished with
exactly the DLWE advantage of the encryption reduction [GSW13, Section 3.2, Lemma 1; Pei16,
Section 6.1.3].

**Proof sketch.** As `Regev.real_uniformKey_advantage`, with the reassociation of the
independent key, coin-matrix and distinguisher seeds done by `acceptProb_bind`: the reduction
is `D` after the coin-using map `(pk, R) ↦ view P μ pk R` (`reduction_eq`), so on `LWE.sample`
and on a uniform key it accepts exactly as `D` accepts `realView` and `uniformKeyView`
(`realView_eq`, `uniformKeyView_eq`). Then read `LWE.decisionAdvantage_eq` and `distAdv_def`. -/
theorem real_uniformKey_advantage {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ) (uniformKeyView P μ) D =
      LWE.decisionAdvantage P.lwe χ (reduction P μ D) := by
  have hred : reduction P μ D = fun pk c => D (view P μ pk c.1) c.2 := by
    funext pk c
    exact reduction_eq P μ D pk c
  have hreal : acceptProb (LWE.sample P.lwe χ) (reduction P μ D) =
      acceptProb (realView P χ μ) D := by
    rw [hred, acceptProb_bind]
    exact congrArg (fun X => acceptProb X D) (funext fun r => (realView_eq P χ μ r).symm)
  have hkey : acceptProb (id : (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension)
      (ZMod P.lwe.modulus) × (Fin P.lwe.samples → ZMod P.lwe.modulus)) → _) (reduction P μ D) =
      acceptProb (uniformKeyView P μ) D := by
    rw [hred, acceptProb_bind]
    exact congrArg (fun X => acceptProb X D) (funext fun r => (uniformKeyView_eq P μ r).symm)
  rw [LWE.decisionAdvantage_eq, distAdv_def, distAdv_def, hreal, hkey]

/-- **Statistical hybrid.** Under a uniform key the view is within `N · ε_LHL` of a fully
uniform key-and-ciphertext pair, where `ε_LHL = ½·√(q^{n+1}/2^m)` is the existing
`Regev.extractionError` [GSW13, Section 3.2, "`R · A` is statistically uniform by the
leftover hash lemma"; Pei16, Section 6.1.3].

**Proof sketch.** As `Regev.uniformKey_uniform_advantage_le`. Relabel the key by the
bijection `Regev.augmented_bijective`, which keeps the whole public key. The ciphertext is
`hashColumns (columnHashParameters P) N Ā R + μG` (`encrypt_eq`, `hashColumns_eq_mul`,
`lift_apply`); translation by `μG` (`Equiv.addRight`) is a bijection of the ciphertext space, so
after relabelling both samplers (`acceptProb_comp_equiv`) the gap is that of `(Ā, ĀR)` versus
`(Ā, U)` for the test that undoes both relabellings before running `D`. Apply
`distAdv_hashColumns_uniform_le` to that test and rewrite its bound with the
`columnHashParameters` readers and `Regev.extractionError_eq`. -/
theorem uniformKey_uniform_advantage_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (uniformKeyView P μ)
      (id : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
        (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → _) D ≤
      P.columns * Regev.extractionError P.lwe := by
  -- Step 1: the key relabelling `pk ↦ Ā`, the ciphertext translation by `μG`, and the test.
  let Key := Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
    (Fin P.lwe.samples → ZMod P.lwe.modulus)
  let AugKey := Matrix (Fin (P.lwe.dimension + 1)) (Fin P.lwe.samples) (ZMod P.lwe.modulus)
  let Coins := Matrix (Fin P.lwe.samples) (Fin P.columns) Bool
  let keyEquiv : Key ≃ AugKey :=
    Equiv.ofBijective (Regev.augmented P.lwe) (Regev.augmented_bijective P.lwe)
  let shift : Ciphertext P := (μ.toNat : ZMod P.lwe.modulus) • gadget P
  let unpack : AugKey × Ciphertext P ≃ Key × Ciphertext P :=
    keyEquiv.symm.prodCongr (Equiv.addRight shift)
  let keySeeds : Key × Coins ≃ AugKey × Coins := keyEquiv.prodCongr (Equiv.refl Coins)
  let sampleHash (r : AugKey × Coins) : AugKey × Ciphertext P :=
    (r.1, Hashing.SIS.hashColumns (columnHashParameters P) P.columns r.1 r.2)
  let test (v : AugKey × Ciphertext P) (coins : ρ) : Bool := D (unpack v) coins
  -- Step 2: the ciphertext is the column hash of the augmented key, translated by `μG`.
  have hsampler : uniformKeyView P μ = fun r => unpack (sampleHash (keySeeds r)) := by
    funext r
    have hlift : (Matrix.of fun c j => ((r.2 c j).toNat : ZMod P.lwe.modulus)) = lift P r.2 := by
      ext c j
      rw [Matrix.of_apply, lift_apply]
    have hhash : Hashing.SIS.hashColumns (columnHashParameters P) P.columns (keyEquiv r.1) r.2 =
        Regev.augmented P.lwe r.1 * lift P r.2 := by
      rw [Hashing.SIS.hashColumns_eq_mul, ← hlift]
      rfl
    rw [uniformKeyView_eq, view_eq, encrypt_eq]
    refine Prod.ext (keyEquiv.symm_apply_apply r.1).symm ?_
    exact (congrArg (· + shift) hhash).symm
  -- Step 3: relabel both samplers; the gap becomes that of `(Ā, ĀR)` versus `(Ā, U)`.
  have hreal : acceptProb (uniformKeyView P μ) D = acceptProb sampleHash test := by
    rw [hsampler]
    simpa only [acceptProb_def] using
      acceptProb_comp_equiv keySeeds (fun r => unpack (sampleHash r)) D
  have hideal : acceptProb (id : Key × Ciphertext P → Key × Ciphertext P) D =
      acceptProb (id : AugKey × Ciphertext P → AugKey × Ciphertext P) test := by
    simpa only [acceptProb_def, id_eq] using
      (acceptProb_comp_equiv unpack (id : Key × Ciphertext P → Key × Ciphertext P) D).symm
  -- Step 4: the column hybrid, its bound read through the `columnHashParameters` readers.
  have hbound := Hashing.SIS.distAdv_hashColumns_uniform_le (columnHashParameters P) P.columns test
  rw [distAdv_def] at hbound ⊢
  rw [hreal, hideal, Regev.extractionError_eq]
  simpa only [columnHashParameters_modulus, columnHashParameters_dimension,
    columnHashParameters_columns] using hbound

/-- **Concrete IND-CPA bound for public-key GSW** [GSW13, Section 3.2 and Lemma 1; Pei16,
Section 6.1.3]. The views of two fixed bits differ by at most two DLWE advantages plus
`2·N·ε_LHL`.

**Proof sketch.** Insert both uniform-key views and the common uniform view; the triangle
inequality (`abs_sub_le`, three times) gives the two exact DLWE terms
(`real_uniformKey_advantage`) and two statistical terms (`uniformKey_uniform_advantage_le`), as
in `Regev.distAdv_encrypt_le`; `linarith` adds them up. -/
theorem distAdv_encrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ₀ μ₁ : Bool)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ₀) (realView P χ μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
      LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) +
      2 * (P.columns * Regev.extractionError P.lwe) := by
  let View := (Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
    (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P
  let ideal : View → View := id
  -- The two exact DLWE terms and the two statistical terms.
  have hkey₀ := real_uniformKey_advantage P χ μ₀ D
  have hkey₁ := real_uniformKey_advantage P χ μ₁ D
  have hstat₀ : distAdv (uniformKeyView P μ₀) ideal D ≤
      P.columns * Regev.extractionError P.lwe :=
    uniformKey_uniform_advantage_le P μ₀ D
  have hstat₁ : distAdv (uniformKeyView P μ₁) ideal D ≤
      P.columns * Regev.extractionError P.lwe :=
    uniformKey_uniform_advantage_le P μ₁ D
  -- The chain `real μ₀ → uniform-key μ₀ → uniform → uniform-key μ₁ → real μ₁`.
  have htriangle₀ := abs_sub_le (acceptProb (realView P χ μ₀) D)
    (acceptProb (uniformKeyView P μ₀) D) (acceptProb (realView P χ μ₁) D)
  have htriangle₁ := abs_sub_le (acceptProb (uniformKeyView P μ₀) D)
    (acceptProb ideal D) (acceptProb (realView P χ μ₁) D)
  have htriangle₂ := abs_sub_le (acceptProb ideal D)
    (acceptProb (uniformKeyView P μ₁) D) (acceptProb (realView P χ μ₁) D)
  rw [abs_sub_comm (acceptProb ideal D) (acceptProb (uniformKeyView P μ₁) D),
    abs_sub_comm (acceptProb (uniformKeyView P μ₁) D) (acceptProb (realView P χ μ₁) D)]
    at htriangle₂
  rw [distAdv_def] at hkey₀ hkey₁ hstat₀ hstat₁ ⊢
  linarith only [hkey₀, hkey₁, hstat₀, hstat₁, htriangle₀, htriangle₁, htriangle₂]

/-- With residue width `w` (`q ≤ 2^w`) and `m ≥ (n+1)·w + 2κ` rows, the statistical term is at
most `N · 2^{−κ}` [GSW13, Section 3.2, "it suffices to take `m > 2n log q`", explicit
repository budget].

**Proof sketch.** `distAdv_encrypt_le` and `Regev.two_extractionError_le`, multiplying the
latter by `N ≥ 0` (`mul_le_mul_of_nonneg_left`). -/
theorem distAdv_encrypt_le_of_width {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : LWE.Noise) (μ₀ μ₁ : Bool) (w κ : ℕ)
    (hq : P.lwe.modulus ≤ 2 ^ w)
    (hm : (P.lwe.dimension + 1) * w + 2 * κ ≤ P.lwe.samples)
    (D : ((Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus)) × Ciphertext P) → ρ → Bool) :
    distAdv (realView P χ μ₀) (realView P χ μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (reduction P μ₀ D) +
      LWE.decisionAdvantage P.lwe χ (reduction P μ₁ D) +
      P.columns * ((2 : ℝ)⁻¹) ^ κ := by
  have h := distAdv_encrypt_le P χ μ₀ μ₁ D
  have hw := Regev.two_extractionError_le P.lwe w κ hq hm
  have hN : 2 * ((P.columns : ℝ) * Regev.extractionError P.lwe) ≤
      P.columns * ((2 : ℝ)⁻¹) ^ κ := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
  linarith only [h, hN]

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW


run_cmd do
  let label := "final_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Security_B_coe"
  Lean.logInfo m!"GSWSEC-EOF {label}"
