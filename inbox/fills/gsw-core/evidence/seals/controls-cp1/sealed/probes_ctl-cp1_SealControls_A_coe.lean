import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "ctl_probes_ctl-cp1_SealControls_A_coe"
  let includeEval := false
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


/-!
Paired Rule 10 seal controls for the gsw-core fill (probe, not library code).

Every `example` is tagged `CTL-<name>-<kind>` in the comment line before it:
* `POS`: reads through a published reader or notation; must pass unsealed and in all four seals.
* `NEG`: unfolds a foreign definition by `rfl`; must pass unsealed and fail exactly once in every
  sealed variant.
* No `PolyExpr.eval` control: `Complexity.PolyExpr` is outside the import closure of every
  owned file (and of this probe), so seals A and B install the same set; the catalogs show it.
* `COE`: a projection coercion (`FinDist`'s `⟨FinDist.prob⟩`); passes unsealed, A_coe, B_coe;
  fails once in strict variants.
The type-level negatives use the five definitions plan §G8 names (`Regev.augmented`,
`LWE.sample`, `Lossy.gadget`, `Randomized.blocksEquiv`, `BitEncoding.codepoint`) and the
owned files' own `gadget`, `Encrypts` and `mul`, which are foreign here.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

-- CTL-gadget-POS
example (P : Parameters) (i : Fin (P.lwe.dimension + 1)) (j : Fin P.columns) :
    gadget P i j = ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
      ZMod P.lwe.modulus) := gadget_apply P i j
-- CTL-gadget-NEG
example (P : Parameters) (i : Fin (P.lwe.dimension + 1)) (j : Fin P.columns) :
    gadget P i j = ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
      ZMod P.lwe.modulus) := rfl
-- CTL-mul-POS
example (P : Parameters) (C₁ C₂ : Ciphertext P) :
    mul P C₁ C₂ = C₁ * lift P (decompose P C₂) := mul_eq P C₁ C₂
-- CTL-mul-NEG
example (P : Parameters) (C₁ C₂ : Ciphertext P) :
    mul P C₁ C₂ = C₁ * lift P (decompose P C₂) := rfl
-- CTL-Encrypts-NEG
example (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (C : Ciphertext P)
    (h : Encrypts P t 0 0 C) : ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ 0) ∧
      Matrix.vecMul t C = ((0 : ℤ) : ZMod P.lwe.modulus) • Matrix.vecMul t (gadget P) +
        fun j => (e j : ZMod P.lwe.modulus) := h
-- CTL-augmented-POS
example (P : Parameters) (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension)
    (ZMod P.lwe.modulus) × (Fin P.lwe.samples → ZMod P.lwe.modulus)) :
    Regev.augmented P.lwe pk = Fin.snoc pk.1.transpose pk.2 := Regev.augmented_eq P.lwe pk
-- CTL-augmented-NEG
example (P : Parameters) (pk : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension)
    (ZMod P.lwe.modulus) × (Fin P.lwe.samples → ZMod P.lwe.modulus)) :
    Regev.augmented P.lwe pk = Fin.snoc pk.1.transpose pk.2 := rfl
-- CTL-sample-POS
example (P : Parameters) (χ : LWE.Noise)
    (r : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) :
    (LWE.sample P.lwe χ r).1 = r.1 := LWE.sample_fst P.lwe χ r
-- CTL-sample-NEG
example (P : Parameters) (χ : LWE.Noise)
    (r : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins))) :
    (LWE.sample P.lwe χ r).1 = r.1 := rfl
-- CTL-lossyGadget-NEG
example (b w : ℕ) (i : Fin (w * b)) (j : Fin w) :
    TrapdoorFunctions.Lossy.gadget b w i j =
      (let jk : Fin w × Fin b := finProdFinEquiv.symm i
       if jk.1 = j then 2 ^ (jk.2 : ℕ) else 0) := rfl
-- CTL-blocksEquiv-NEG
example (n b : ℕ) : Randomized.blocksEquiv n b =
    ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.curry _ _ _)).trans (Equiv.arrowCongr (Equiv.refl _) (Randomized.bitsEquiv b)) :=
  rfl
-- CTL-codepoint-POS
example (P : Parameters) : LWE.BitEncoding.codepoint P.lwe true =
    if true then ((P.lwe.modulus / 2 : ℕ) : ZMod P.lwe.modulus) else 0 :=
  LWE.BitEncoding.codepoint_eq P.lwe true
-- CTL-codepoint-NEG
example (P : Parameters) : LWE.BitEncoding.codepoint P.lwe true =
    if true then ((P.lwe.modulus / 2 : ℕ) : ZMod P.lwe.modulus) else 0 := rfl
-- CTL-columns-POS
example (P : Parameters) : P.columns = (P.lwe.dimension + 1) * P.width := rfl
-- CTL-coe-COE
example {α : Type} [Fintype α] (d : InformationTheory.FinDist α) (a : α) :
    d a = d.prob a := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW


run_cmd do
  let label := "ctl_probes_ctl-cp1_SealControls_A_coe"
  Lean.logInfo m!"GSWCORE-EOF {label}"
