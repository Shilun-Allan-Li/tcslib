/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.LWE.Experiments
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "base_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Symmetric_B_strict"
  let includeEval := true
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
# Secret-key GSW: batched encryption under one secret, and its DLWE security

## Main definitions

* `rowEquiv`: split `m = k·N` LWE rows into `k` blocks of `N`.
* `symEncrypt`: `k` ciphertexts `Cᵢ = Āᵢ + μᵢ G` from one LWE challenge, block `i` of the
  augmented sample matrix supplying `Āᵢ`; one common secret for all of them.

## Main results

* `encrypts_symEncrypt`: every secret-key ciphertext has noise at most `B` (not `m·B`).
* `distAdv_symEncrypt_le`: two message vectors' batches differ by at most two DLWE
  advantages with `k·N` rows; no leftover hashing.

## References

* [AP14] J. Alperin-Sheriff, C. Peikert, ePrint 2014/094 version dated 13 June 2014,
  Section 3.2 (`GSW.Enc`: "a fresh ciphertext is just `μG` plus a matrix of `nℓ` independent
  LWE samples").
* [BV14] Z. Brakerski, V. Vaikuntanathan, ePrint 2013/541, Section 3.1 (`NCCrypt.SecEnc`:
  "a secret-key encryption of `μ` is somewhat less noisy than a public-key encryption").
* [Wu24] D. Wu, CS395T lecture notes, Spring 2024, Definition 20.5 (the batched direct
  pattern of the existing symmetric Regev scheme).

**Deviations.** The secret is uniform ([AP14] draws it from the error law, which needs a
separate normal-form assumption excluded by plan decision D1). The batch of `k` ciphertexts
uses one DLWE instance with exactly `k·N` rows, so multi-message security is part of the
statement rather than a further hybrid. Row reindexing goes through the published equivalence
`rowEquiv`, the domain-equivalence pattern used elsewhere for type-valued parameters.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open Encryption.PublicKey

/-- Split `m = k·N` LWE rows into `k` blocks of `N` consecutive rows. Technical glue. -/
def rowEquiv (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) :
    Fin k × Fin P.columns ≃ Fin P.lwe.samples :=
  finProdFinEquiv.trans (finCongr hN.symm)

/-- `rowEquiv P hN` is `finProdFinEquiv` followed by the cast along `hN`. -/
theorem rowEquiv_eq (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) :
    rowEquiv P hN = finProdFinEquiv.trans (finCongr hN.symm) := rfl

/-- Batched secret-key GSW encryption [AP14, Section 3.2, `GSW.Enc`; BV14, Section 3.1,
`NCCrypt.SecEnc`, gadget form]: from an LWE challenge `(A, b)` with `k·N` rows, ciphertext `i`
is the block-`i` columns of the augmented matrix plus `μᵢ G`. -/
def symEncrypt (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (c : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Fin k → Bool) : Fin k → Ciphertext P :=
  fun i => (Regev.augmented P.lwe c).submatrix id (fun j => rowEquiv P hN (i, j)) +
    ((μ i).toNat : ZMod P.lwe.modulus) • gadget P

/-- Ciphertext `i` is the reindexed block of the augmented challenge plus `μᵢ G`. -/
theorem symEncrypt_apply (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (c : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      (Fin P.lwe.samples → ZMod P.lwe.modulus))
    (μ : Fin k → Bool) (i : Fin k) :
    symEncrypt P hN c μ i = (Regev.augmented P.lwe c).submatrix id (fun j => rowEquiv P hN (i, j)) +
      ((μ i).toNat : ZMod P.lwe.modulus) • gadget P := rfl

/-- **Secret-key noise.** On a real LWE challenge with row errors bounded by `B`, every
secret-key ciphertext encrypts its bit under `t = (−s,1)` with noise at most `B` [AP14,
Section 3.2, "Notice that `sᵗC = eᵗ + μ·sᵗG`"; BV14, Section 3.1].

**Proof sketch.** `Matrix.vecMul_add`, `Matrix.vecMul_smul`; the block of `tᵗ Ā` is
`tᵗ Ā` read at the reindexed columns (`Matrix.vecMul` of a `submatrix`), equal to
`e ∘ rowEquiv` by `vecMul_secretVector_augmented`. -/
theorem encrypts_symEncrypt (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns)
    (A : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus))
    (s : Fin P.lwe.dimension → ZMod P.lwe.modulus) (e : Fin P.lwe.samples → ℤ) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (μ : Fin k → Bool) (i : Fin k) :
    Encrypts P (secretVector P s) ((μ i).toNat : ℤ) B
      (symEncrypt P hN (A, LWE.noisyValues P.lwe A s e) μ i) := by
  sorry

/-- **Concrete IND-CPA bound for batched secret-key GSW** [AP14, Section 3.2, "The IND-CPA
security of the scheme follows immediately from the assumed hardness of LWE"; Wu24,
Lecture 21, the two-hybrid pattern]. For two message vectors, the distributions of the `k`
ciphertexts under one uniform secret differ by at most two DLWE advantages with `k·N` rows.

**Proof sketch.** As `Encryption.Symmetric.Regev.distAdv_encrypt_le`: each real batch is
`symEncrypt` of the actual LWE sample; on the uniform side, `(A,b) ↦ symEncrypt P hN (A,b) μ`
is a bijection onto `Fin k → Ciphertext P` (`Regev.augmented_bijective`, the column
reindexing by `rowEquiv`, and translation by `μG`; both sides have `q^{(n+1)·k·N}` elements),
so both ideal acceptance probabilities equal that of a uniform batch.
Insert it between the two real experiments and use the triangle inequality. -/
theorem distAdv_symEncrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) {k : ℕ} (hN : P.lwe.samples = k * P.columns) (χ : LWE.Noise)
    (μ₀ μ₁ : Fin k → Bool) (D : (Fin k → Ciphertext P) → ρ → Bool) :
    distAdv (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₀)
        (fun r => symEncrypt P hN (LWE.sample P.lwe χ r) μ₁) D ≤
      LWE.decisionAdvantage P.lwe χ (fun c r => D (symEncrypt P hN c μ₀) r) +
      LWE.decisionAdvantage P.lwe χ (fun c r => D (symEncrypt P hN c μ₁) r) := by
  sorry

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW


run_cmd do
  let label := "base_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Symmetric_B_strict"
  Lean.logInfo m!"GSWCORE-EOF {label}"
