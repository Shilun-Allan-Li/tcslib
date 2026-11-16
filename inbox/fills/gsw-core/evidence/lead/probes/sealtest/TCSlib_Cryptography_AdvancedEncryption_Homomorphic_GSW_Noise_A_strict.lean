/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Gadget
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "t_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Noise_A_strict"
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
# The GSW noise invariant and its homomorphic operations

## Main definitions

* `Encrypts P t x β C`: `tᵗ C = x · tᵗ G + eᵗ (mod q)` for an integer error vector `e` with
  every entry of magnitude at most `β`. This is the key-agnostic invariant of [AP14,
  Definitions 3.2–3.3] with an explicit worst-case bound.
* `mul`: `C₁ ⊡ C₂ = C₁ · G⁻¹(C₂)`; `nand`: `G − C₁ ⊡ C₂`; `chain`: the right-associative
  product `C₁ ⊡ (C₂ ⊡ (⋯ ⊡ acc))`.

## Main results

* `encrypts_gadget`, `encrypts_zero`: `G` encrypts `1` and `0` encrypts `0`, both noiseless.
* `Encrypts.add`, `.neg`, `.sub`, `.sum`, `.mono`: additive closure.
* `Encrypts.mul`: **asymmetric** multiplication: the left operand's noise is multiplied by
  `N` (a bound on `‖G⁻¹(C₂)‖`), the right operand's only by `|x₁|`.
* `Encrypts.mul_bit`, `Encrypts.mul_le`: the bit-message and symmetric `(N+1)·max` corollaries.
* `Encrypts.nand`: NAND of two bit encryptions with noise `N·β₁ + β₂ ≤ (N+1)·max`.
* `encrypts_chain`: a right-associative chain of `k` bit encryptions times an accumulator has
  noise `β_acc + k·N·β`, additive in `k`.

## References

* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; ePrint 2014/094 version dated 13 June 2014, Section 3.2 (operations),
  Definitions 3.2–3.3, Lemma 3.5, Corollary 3.6.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 6.1.3, Equations (6.1.5)–(6.1.6).
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Sections 1.3.1, 1.3.3, 3.3 (`Add`, `Mult`, `NAND`) and 3.4.
* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-Based FHE as Secure as PKE*, ITCS 2014;
  ePrint 2013/541, Claims 3.4.1–3.4.2.

**Convention and deviations.** Ciphertexts and keys follow [AP14, Section 3.2] and
[Pei16, Section 6.1.3]: `t` is a *left* approximate singular vector, `tᵗ C ≈ x · tᵗ G`, and
multiplication is `C₁ · G⁻¹(C₂)`. Its error is `e₁ᵗ G⁻¹(C₂) + x₁ e₂ᵗ` [AP14, Lemma 3.5]: the
**left** operand's error is expanded, the **right** operand's is scaled by the left message.
[GSW13] and [BV14] use the transposed convention (`C · v ≈ μ v`, square `{0,1}` ciphertexts
after `Flatten`), in which `C₁ · C₂` has error `μ₂ e₁ + C₁ e₂` [GSW13, Section 3.3]: there the
*right* operand's error is expanded. The two conventions are mirror images; a chain with
additive noise puts fresh ciphertexts on the left here, on the right in [BV14, Claim 3.4.2].
Noise bounds are worst-case (`ℓ∞`, `ℕ`-valued), not [AP14]'s subgaussian parameters, so a
`k`-fold chain grows like `k·N·β` rather than `√k`. [GSW13]'s NAND is `I_N − C₁·C₂` after
`Flatten`; here it is `G − C₁·G⁻¹(C₂)`, with the same `(N+1)·B` bound [GSW13, Section 3.4].
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

/-- Homomorphic multiplication `C₁ ⊡ C₂ = C₁ · G⁻¹(C₂)` [AP14, Section 3.2; Pei16,
Equation (6.1.6)]. Deterministic, right operand decomposed. -/
def mul (P : Parameters) (C₁ C₂ : Ciphertext P) : Ciphertext P :=
  C₁ * lift P (decompose P C₂)

/-- `mul P C₁ C₂` is `C₁` times the lifted binary decomposition of `C₂`. -/
theorem mul_eq (P : Parameters) (C₁ C₂ : Ciphertext P) :
    mul P C₁ C₂ = C₁ * lift P (decompose P C₂) := rfl

/-- Homomorphic NAND `G − C₁ ⊡ C₂` [GSW13, Section 3.3, `NAND`, gadget form; Pei16,
Section 6.1.3, "`(x₁ NAND x₂) = 1 − x₁x₂`"]. -/
def nand (P : Parameters) (C₁ C₂ : Ciphertext P) : Ciphertext P :=
  gadget P - mul P C₁ C₂

/-- `nand P C₁ C₂` is the gadget minus the homomorphic product. -/
theorem nand_eq (P : Parameters) (C₁ C₂ : Ciphertext P) :
    nand P C₁ C₂ = gadget P - mul P C₁ C₂ := rfl

/-- The right-associative product chain `C₁ ⊡ (C₂ ⊡ (⋯ ⊡ (Cₖ ⊡ acc)))` [AP14, Corollary 3.6,
with `acc = G`; Pei16, Section 6.1.3, "Bootstrapping": right-associative chains]. -/
def chain (P : Parameters) (Cs : List (Ciphertext P)) (acc : Ciphertext P) : Ciphertext P :=
  Cs.foldr (mul P) acc

/-- The empty chain is its accumulator. -/
theorem chain_nil (P : Parameters) (acc : Ciphertext P) : chain P [] acc = acc := rfl

/-- A nonempty chain multiplies its head on the left of the remaining chain. -/
theorem chain_cons (P : Parameters) (C : Ciphertext P) (Cs : List (Ciphertext P))
    (acc : Ciphertext P) : chain P (C :: Cs) acc = mul P C (chain P Cs acc) := rfl

/-- **The GSW noise invariant.** `C` encrypts the integer `x` under the key vector `t` with
noise at most `β`: there is an integer error vector `e`, every entry of magnitude at most
`β`, with `tᵗ C = x · tᵗ G + eᵗ` modulo `q` [AP14, Definitions 3.2–3.3; Pei16, Section 6.1.3,
`sᵗ A ≈ x · sᵗ G`; BV14, Definition 3.1, transposed]. The predicate does not fix how `C` was
produced, so it is shared by public-key, secret-key and evaluated ciphertexts. -/
def Encrypts (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ)
    (β : ℕ) (C : Ciphertext P) : Prop :=
  ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ β) ∧
    Matrix.vecMul t C = (x : ZMod P.lwe.modulus) • Matrix.vecMul t (gadget P) +
      fun j => (e j : ZMod P.lwe.modulus)

/-- `Encrypts P t x β C` holds exactly when some `β`-bounded integer error vector `e` gives
`tᵗ C = x · tᵗ G + e`. -/
theorem encrypts_iff (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus)
    (x : ℤ) (β : ℕ) (C : Ciphertext P) :
    Encrypts P t x β C ↔ ∃ e : Fin P.columns → ℤ, (∀ j, (e j).natAbs ≤ β) ∧
      Matrix.vecMul t C = (x : ZMod P.lwe.modulus) • Matrix.vecMul t (gadget P) +
        fun j => (e j : ZMod P.lwe.modulus) := Iff.rfl

section Closure

variable (P : Parameters) {t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus}

/-- The gadget encrypts `1` with zero noise [AP14, Section 3.3, "`μG` … has error 0"].

**Proof sketch.** Take `e = 0`; `1 • v + 0 = v`. -/
theorem encrypts_gadget : Encrypts P t 1 0 (gadget P) := by
  sorry

/-- The zero matrix encrypts `0` with zero noise [AP14, Section 3.3].

**Proof sketch.** Take `e = 0`; `Matrix.vecMul_zero` and `zero_smul`. -/
theorem encrypts_zero : Encrypts P t 0 0 0 := by
  sorry

/-- Weakening the noise bound preserves the invariant.

**Proof sketch.** Reuse the witness; `le_trans` on each entry. -/
theorem Encrypts.mono {x : ℤ} {β β' : ℕ} {C : Ciphertext P} (h : Encrypts P t x β C)
    (hβ : β ≤ β') : Encrypts P t x β' C := by
  sorry

/-- Homomorphic addition adds messages and noise bounds [AP14, Lemma 3.5, first claim;
GSW13, Section 3.3, `Add`; BV14, Claim 3.4.1].

**Proof sketch.** Witness `e₁ + e₂`. `Matrix.vecMul_add` splits `tᵗ(C₁+C₂)`; `add_smul` and
`Int.cast_add` regroup; `Int.natAbs_add_le` bounds the entries. -/
theorem Encrypts.add {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ + x₂) (β₁ + β₂) (C₁ + C₂) := by
  sorry

/-- Negation negates the message and keeps the noise bound.

**Proof sketch.** Witness `-e`; `Matrix.vecMul_neg`, `neg_smul`, `Int.natAbs_neg`. -/
theorem Encrypts.neg {x : ℤ} {β : ℕ} {C : Ciphertext P} (h : Encrypts P t x β C) :
    Encrypts P t (-x) β (-C) := by
  sorry

/-- Subtraction subtracts messages and adds noise bounds.

**Proof sketch.** `sub_eq_add_neg`, then `Encrypts.add` and `Encrypts.neg`. -/
theorem Encrypts.sub {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ - x₂) (β₁ + β₂) (C₁ - C₂) := by
  sorry

/-- A finite sum of encryptions encrypts the sum of the messages with the sum of the noise
bounds [AP14, Section 4.1, Equation (4.1), the outer homomorphic sum].

**Proof sketch.** `Finset.induction_on`; the empty sum is `encrypts_zero`, and each insertion
is `Encrypts.add`. -/
theorem Encrypts.sum {ι : Type*} (s : Finset ι) (x : ι → ℤ) (β : ι → ℕ)
    (C : ι → Ciphertext P) (h : ∀ i ∈ s, Encrypts P t (x i) (β i) (C i)) :
    Encrypts P t (∑ i ∈ s, x i) (∑ i ∈ s, β i) (∑ i ∈ s, C i) := by
  sorry

/-- **Asymmetric homomorphic multiplication** [AP14, Lemma 3.5; Pei16, Equation (6.1.6);
BV14, Claim 3.4.2, mirrored]. If `C₁` encrypts `x₁` with noise `β₁` and `C₂` encrypts `x₂`
with noise `β₂`, then `C₁ ⊡ C₂` encrypts `x₁x₂` with noise at most `N·β₁ + |x₁|·β₂`. The left
operand's noise is multiplied by `N`, the number of `{0,1}` entries in a column of `G⁻¹(C₂)`;
the right operand's is multiplied only by the left message.

**Proof sketch.** `Matrix.vecMul_vecMul` rewrites `tᵗ (C₁ X)` as `(tᵗ C₁) X` with
`X = lift (G⁻¹ C₂)`. Substitute `h₁`: `(x₁ tᵗG + e₁ᵗ) X = x₁ tᵗ(G X) + e₁ᵗ X`. By
`gadget_mul_decompose`, `G X = C₂`, so the first term is `x₁ tᵗ C₂ = x₁x₂ tᵗG + x₁ e₂ᵗ` by `h₂`.
The witness is `j ↦ (∑ᵢ e₁ i · X i j) + x₁ · e₂ j`. The first summand is a binary subset sum of
`N` entries bounded by `β₁`, bounded by `N·β₁` via `LWE.binaryErrorSum_bound`; the second has
magnitude `|x₁|·|e₂ j| ≤ |x₁|·β₂` (`Int.natAbs_mul`). -/
theorem Encrypts.mul {x₁ x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t x₁ β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t (x₁ * x₂) (P.columns * β₁ + x₁.natAbs * β₂) (mul P C₁ C₂) := by
  sorry

/-- For a bit message on the left, multiplication has noise `N·β₁ + β₂` [GSW13, Section 3.3,
`Mult`; Pei16, Section 6.1.3].

**Proof sketch.** `Encrypts.mul` and `Encrypts.mono`, since `(b.toNat : ℤ).natAbs ≤ 1`. -/
theorem Encrypts.mul_bit {b : Bool} {x₂ : ℤ} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t (b.toNat : ℤ) β₁ C₁) (h₂ : Encrypts P t x₂ β₂ C₂) :
    Encrypts P t ((b.toNat : ℤ) * x₂) (P.columns * β₁ + β₂) (GSW.mul P C₁ C₂) := by
  sorry

/-- Symmetric corollary: two bit-message operands with noise at most `β` give a product with
noise at most `(N+1)·β` [GSW13, Section 3.4; Pei16, Section 6.1.3].

**Proof sketch.** `Encrypts.mul_bit` and `N·β + β = (N+1)·β`. -/
theorem Encrypts.mul_le {b₁ b₂ : Bool} {β : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t (b₁.toNat : ℤ) β C₁) (h₂ : Encrypts P t (b₂.toNat : ℤ) β C₂) :
    Encrypts P t ((b₁ && b₂).toNat : ℤ) ((P.columns + 1) * β) (GSW.mul P C₁ C₂) := by
  sorry

/-- **Homomorphic NAND** [GSW13, Sections 3.3–3.4, `NAND`, "the error is increased by a
factor of at most `N + 1`"; Pei16, Section 6.1.3]. Bit encryptions with noise `β₁`, `β₂` give
an encryption of `NAND(b₁,b₂)` with noise at most `N·β₁ + β₂`.

**Proof sketch.** `encrypts_gadget`, `Encrypts.mul_bit`, `Encrypts.sub`; the message
`1 − b₁b₂` equals `(!(b₁ && b₂)).toNat` by cases on the bits. -/
theorem Encrypts.nand {b₁ b₂ : Bool} {β₁ β₂ : ℕ} {C₁ C₂ : Ciphertext P}
    (h₁ : Encrypts P t (b₁.toNat : ℤ) β₁ C₁) (h₂ : Encrypts P t (b₂.toNat : ℤ) β₂ C₂) :
    Encrypts P t ((!(b₁ && b₂)).toNat : ℤ) (P.columns * β₁ + β₂) (nand P C₁ C₂) := by
  sorry

/-- **Product chains grow additively** [AP14, Corollary 3.6, worst-case form; Pei16,
Section 6.1.3, "any polynomial-length chain of homomorphic bit-multiplications on fresh
ciphertexts, if done in a right-associative manner, incurs only polynomial error growth";
BV14, Claim 3.4.2 and the proof of Lemma 3.6, mirrored]. If every `Cᵢ` encrypts the bit `bᵢ`
with noise at most `β` and `acc` encrypts `x` with noise `β₀`, then
`C₁ ⊡ (⋯ ⊡ (Cₖ ⊡ acc))` encrypts `(∏ bᵢ)·x` with noise at most `β₀ + k·N·β`.

**Proof sketch.** Induction on the list. The step is `Encrypts.mul_bit` with the head on the
left: noise `N·β + (previous)`, message `b · (∏ rest · x)`; reassociate the product and the
sum `β₀ + (k+1)·N·β`. -/
theorem encrypts_chain {bs : List Bool} {Cs : List (Ciphertext P)} {β β₀ : ℕ} {x : ℤ}
    {acc : Ciphertext P}
    (hs : List.Forall₂ (fun b C => Encrypts P t (b.toNat : ℤ) β C) bs Cs)
    (hacc : Encrypts P t x β₀ acc) :
    Encrypts P t (((bs.all id).toNat : ℤ) * x) (β₀ + Cs.length * (P.columns * β))
      (chain P Cs acc) := by
  sorry

end Closure

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW


run_cmd do
  let label := "t_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Noise_A_strict"
  Lean.logInfo m!"GSWCORE-EOF {label}"
