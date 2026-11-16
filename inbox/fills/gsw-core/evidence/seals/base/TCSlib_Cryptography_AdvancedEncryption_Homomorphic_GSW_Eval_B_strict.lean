/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "base_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Eval_B_strict"
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
# Homomorphic evaluation of the library's Boolean circuits, and leveled correctness

## Main definitions

* `homAnd`: `[] ↦ G`, `[C] ↦ C`, `C :: Cs ↦ C ⊡ homAnd Cs` (a product chain).
* `homNot`: `G − homAnd`; `homOr`: `G − homAnd (map (G − ·))` (De Morgan).
* `homGate`: the homomorphic counterpart of `BoolCircuit.DAGGate.eval`, gate kind by gate kind.
* `evalValues`, `eval`: run `homGate` over a `BoolCircuit.DAGCircuit` with the existing
  `BoolCircuit.runWith` host, and read the output vertex.

## Main results

* `homAnd_encrypts`, `homGate_encrypts`: per-gate noise `(N+1)·β` for fan-in at most two.
* `eval_encrypts`: a fan-in-two circuit of depth `d` maps `β`-noisy bit encryptions to a
  `(N+1)^d·β`-noisy encryption of its output [GSW13, Section 3.3, "Circuits"].
* `decrypt_keygen_eval`: **leveled correctness** for depth `≤ L` whenever
  `2·(ℓ·((N+1)^L·(m·B))) < ⌊q/2⌋`, for every key, input and coin.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.3 ("Circuits": error `(N+1)^L · B` for NAND-depth `L`) and Section 3.4 (condition
  `q/B > 8(N+1)^L`).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009, Definition 6.1 (the circuit model of `DAGCircuit`).
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 6.1.3 (NAND as `1 − x₁x₂`).

**Deviations.** The circuit model is the library's `DAGCircuit` (`∧`, `∨`, `¬` gates of
fan-in at most two), not a NAND-only circuit: `∧` is one GSW product, `¬` is `G − ·`, `∨` is
De Morgan through two negations, so every gate costs at most one product and the bound
`(N+1)^depth · β` of [GSW13, Section 3.3] holds with the library's own `depth`. [GSW13]'s
"NAND-depth" and the library's depth differ by at most a constant factor for a translated
circuit. Correctness is every-coin under a worst-case bound, not with overwhelming
probability. The relation to [GSW13, Section 3.4]'s `q/B > 8(N+1)^L`: here the decryption
condition carries an extra factor `ℓ` (one for `q = 2^ℓ`) and the fresh noise is `m·B`.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

/-- Homomorphic conjunction of a list of ciphertexts: the gadget for the empty list, the
ciphertext itself for a singleton, and otherwise a right-associative product chain, each head
multiplied on the left [Pei16, Section 6.1.3; AP14, Corollary 3.6]. The singleton case avoids a
needless product. -/
def homAnd (P : Parameters) : List (Ciphertext P) → Ciphertext P
  | [] => gadget P
  | [C] => C
  | C :: C' :: Cs => mul P C (homAnd P (C' :: Cs))

/-- The empty conjunction is the noiseless encryption `G` of `1`. -/
theorem homAnd_nil (P : Parameters) : homAnd P [] = gadget P := rfl

/-- A one-element conjunction is that ciphertext. -/
theorem homAnd_singleton (P : Parameters) (C : Ciphertext P) : homAnd P [C] = C := rfl

/-- A conjunction of at least two ciphertexts multiplies the head on the left. -/
theorem homAnd_cons_cons (P : Parameters) (C C' : Ciphertext P) (Cs : List (Ciphertext P)) :
    homAnd P (C :: C' :: Cs) = mul P C (homAnd P (C' :: Cs)) := rfl

/-- Homomorphic negated conjunction `G − homAnd Cs`, matching the library's `¬` gate, which
negates the conjunction of its inputs [Pei16, Section 6.1.3, NAND as `1 − x₁x₂`]. -/
def homNot (P : Parameters) (Cs : List (Ciphertext P)) : Ciphertext P :=
  gadget P - homAnd P Cs

/-- `homNot P Cs` is the gadget minus the homomorphic conjunction. -/
theorem homNot_eq (P : Parameters) (Cs : List (Ciphertext P)) :
    homNot P Cs = gadget P - homAnd P Cs := rfl

/-- Homomorphic disjunction by De Morgan: `G − homAnd (G − C₁, …, G − Cₖ)`. -/
def homOr (P : Parameters) (Cs : List (Ciphertext P)) : Ciphertext P :=
  gadget P - homAnd P (Cs.map fun C => gadget P - C)

/-- `homOr P Cs` is the gadget minus the conjunction of the complements. -/
theorem homOr_eq (P : Parameters) (Cs : List (Ciphertext P)) :
    homOr P Cs = gadget P - homAnd P (Cs.map fun C => gadget P - C) := rfl

/-- The homomorphic counterpart of `DAGGate.eval`: read each argument vertex's ciphertext
(the noiseless `0` encryption of `false` out of range, matching `getD … false`) and apply
`homAnd`, `homOr` or `homNot` by gate kind. -/
def homGate (P : Parameters) (g : DAGGate) (cts : List (Ciphertext P)) : Ciphertext P :=
  match g.kind with
  | .and => homAnd P (g.args.map fun a => cts.getD a 0)
  | .or => homOr P (g.args.map fun a => cts.getD a 0)
  | .not => homNot P (g.args.map fun a => cts.getD a 0)

/-- The homomorphic gate dispatches on the gate kind exactly as `DAGGate.eval_eq`. -/
theorem homGate_eq (P : Parameters) (g : DAGGate) (cts : List (Ciphertext P)) :
    homGate P g cts = match g.kind with
      | .and => homAnd P (g.args.map fun a => cts.getD a 0)
      | .or => homOr P (g.args.map fun a => cts.getD a 0)
      | .not => homNot P (g.args.map fun a => cts.getD a 0) := rfl

/-- The ciphertexts of all vertices: the input ciphertexts, then one per gate, computed by
the existing `runWith` host with the homomorphic gate. -/
def evalValues (P : Parameters) {k : ℕ} (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) :
    List (Ciphertext P) :=
  runWith (homGate P) Cc.gates (List.ofFn cts)

/-- `evalValues P Cc cts` runs `homGate P` over the gates from the input ciphertexts. -/
theorem evalValues_eq (P : Parameters) {k : ℕ} (Cc : DAGCircuit k)
    (cts : Fin k → Ciphertext P) :
    evalValues P Cc cts = runWith (homGate P) Cc.gates (List.ofFn cts) := rfl

/-- **Homomorphic circuit evaluation** [GSW13, Section 3.3, "Circuits"; BV14, Definition 2.12
(leveled evaluation)]: the ciphertext at the circuit's output vertex. -/
def eval (P : Parameters) {k : ℕ} (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) :
    Ciphertext P :=
  (evalValues P Cc cts).getD Cc.output 0

/-- `eval P Cc cts` reads the output vertex of `evalValues`. -/
theorem eval_eq (P : Parameters) {k : ℕ} (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) :
    eval P Cc cts = (evalValues P Cc cts).getD Cc.output 0 := rfl

section Correctness

variable (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}

/-- A homomorphic conjunction of `k` bit encryptions, each with noise at most `β`, encrypts
the conjunction of the bits with noise at most `((k−1)·N + 1)·β` (natural subtraction, so
the empty and one-element cases give `β`) [Pei16, Section 6.1.3; AP14, Corollary 3.6].

**Proof sketch.** Induction following `homAnd`'s three equations: `encrypts_gadget` with
`Encrypts.mono` for `[]`, the hypothesis for `[C]`, and `Encrypts.mul_bit` for `C :: C' :: Cs`,
whose bound `N·β + ((k−2)·N+1)·β` equals `((k−1)·N+1)·β`. The message is `List.all` by
`List.all_cons` and `Bool.toNat` of `&&` as a product. -/
theorem homAnd_encrypts {bs : List Bool} {Cs : List (Ciphertext P)} {β : ℕ}
    (hs : List.Forall₂ (fun b C => Encrypts P t (b.toNat : ℤ) β C) bs Cs) :
    Encrypts P t ((bs.all id).toNat : ℤ) (((Cs.length - 1) * P.columns + 1) * β)
      (homAnd P Cs) := by
  sorry

/-- **Per-gate noise.** A gate of fan-in at most two, whose argument vertices hold `β`-noisy
encryptions of their values, produces a `(N+1)·β`-noisy encryption of its value [GSW13,
Section 3.3, `NAND`: "the error is increased by a factor of at most `N + 1`"].

**Proof sketch.** Case on `g.kind` through `homGate_eq` and `DAGGate.eval_eq`. With
`bs = g.args.map (vals.getD · false)` and `Cs = g.args.map (cts.getD · 0)`,
`List.forall₂_map_left_iff` and `List.forall₂_map_right_iff` give the hypothesis of
`homAnd_encrypts`; `List.all_map` matches the messages; `length ≤ 2`
bounds `((k−1)·N+1)·β ≤ (N+1)·β`. For `¬`, subtract from `encrypts_gadget` (`Encrypts.sub`,
noise `0 + ·`). For `∨`, the complements `G − C` keep noise `β`, then one more subtraction;
`Bool` De Morgan identifies the message. -/
theorem homGate_encrypts (g : DAGGate) (hfan : g.args.length ≤ 2) (vals : List Bool)
    (cts : List (Ciphertext P)) (β : ℕ)
    (hargs : ∀ a ∈ g.args, Encrypts P t ((vals.getD a false).toNat : ℤ) β (cts.getD a 0)) :
    Encrypts P t ((g.eval vals).toNat : ℤ) ((P.columns + 1) * β) (homGate P g cts) := by
  sorry

/-- **Depth-indexed noise growth.** For a circuit of fan-in at most two, if every input
ciphertext encrypts its input bit with noise at most `β`, then the output ciphertext
`eval P Cc cts` encrypts the circuit's output with noise at most `(N+1)^{depth}·β` [GSW13,
Section 3.3, "the final ciphertext's error will be bounded by `(N + 1)^L · B`"]. The proof
establishes the stronger invariant `(N+1)^{depthAt v}·β` at every vertex `v` as an intermediate
step.

**Proof sketch.** Apply the shared `runWith_rel` to `DAGGate.eval` from `List.ofFn x` and
`homGate P` from `List.ofFn cts`, with
`R v b C := Encrypts P t b.toNat ((N+1)^{Cc.depthAt v}·β) C`. Inputs: `depthAt_input` gives
depth `0`. Gate `i`: `DAGCircuit.depthAt_gate` writes the gate's depth as
`gs[i].depth Cc.depths`; `DAGGate.getD_lt_depth` puts each argument at depth at most one less,
so the arguments are `(N+1)^{d−1}·β`-noisy (`Encrypts.mono`, `Nat.pow_le_pow_right`), and
`homGate_encrypts` multiplies by `N+1`. The output vertex is in range by `Cc.output_lt`;
`DAGCircuit.eval_eq`, `values_eq` and `depth_eq` identify the two sides. -/
theorem eval_encrypts {k : ℕ} (Cc : DAGCircuit k) (hfan : ∀ g ∈ Cc.gates, g.args.length ≤ 2)
    (x : Fin k → Bool) (cts : Fin k → Ciphertext P) (β : ℕ)
    (hin : ∀ i, Encrypts P t ((x i).toNat : ℤ) β (cts i)) :
    Encrypts P t ((Cc.eval x).toNat : ℤ) ((P.columns + 1) ^ Cc.depth * β) (eval P Cc cts) := by
  sorry

/-- **Leveled correctness of public-key GSW** [GSW13, Sections 3.3–3.4; Pei16, Section 6.1.3].
For every key-generation seed, every fan-in-two circuit of depth at most `L`, every input and
every encryption coin, decrypting the homomorphic evaluation of the input encryptions gives
the circuit's output, provided the noise law is `B`-bounded and
`2·(ℓ·((N+1)^L·(m·B))) < ⌊q/2⌋`.

**Proof sketch.** `encrypts_keygen_encrypt` gives input noise `m·B`; `eval_encrypts` gives
output noise `(N+1)^{depth}·(m·B) ≤ (N+1)^L·(m·B)` (`Encrypts.mono`); `decrypt_of_encrypts`. -/
theorem decrypt_keygen_eval (χ : LWE.Noise)
    (rg : Matrix (Fin P.lwe.samples) (Fin P.lwe.dimension) (ZMod P.lwe.modulus) ×
      ((Fin P.lwe.dimension → ZMod P.lwe.modulus) × (Fin P.lwe.samples → χ.Coins)))
    {k : ℕ} (Cc : DAGCircuit k) (hfan : ∀ g ∈ Cc.gates, g.args.length ≤ 2)
    (x : Fin k → Bool) (R : Fin k → Matrix (Fin P.lwe.samples) (Fin P.columns) Bool)
    (B L : ℕ) (hχ : χ.Bounded B) (hdepth : Cc.depth ≤ L)
    (hsep : 2 * (P.width * ((P.columns + 1) ^ L * (P.lwe.samples * B))) <
      P.lwe.modulus / 2) :
    decrypt P (Regev.keygen P.lwe χ rg).2
        (eval P Cc fun i => encrypt P (Regev.keygen P.lwe χ rg).1 (x i) (R i)) =
      Cc.eval x := by
  sorry

end Correctness

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW


run_cmd do
  let label := "base_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Eval_B_strict"
  Lean.logInfo m!"GSWCORE-EOF {label}"
