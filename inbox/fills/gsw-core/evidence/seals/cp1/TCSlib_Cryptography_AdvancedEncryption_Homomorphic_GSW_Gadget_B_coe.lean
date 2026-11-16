/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.LWE.Basic
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Gadget
import Mathlib.Data.Matrix.Mul
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "cp1_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Gadget_B_coe"
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
# The GSW gadget matrix and its binary decomposition

## Main definitions

* `GSW.Parameters`: an LWE parameter bundle with a gadget width `ℓ` satisfying `q ≤ 2^ℓ`.
* `Parameters.columns`: the ciphertext width `N = (n+1)·ℓ` (a reducible abbreviation).
* `gadget`: the block-diagonal gadget `G = I_{n+1} ⊗ gᵗ` with `g = (1,2,…,2^{ℓ-1})`,
  an `(n+1) × N` matrix modulo `q`.
* `digit`, `decomposeVec`, `decompose`: the deterministic binary decomposition `G⁻¹`,
  little-endian inside each block, returning Boolean matrices.
* `lift`: read a Boolean matrix as a `{0,1}` matrix modulo `q`.

## Main results

* `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`: `G · G⁻¹(M) = M` [Pei16, (5.4.1)].
* `decomposeVec_block_eq_false`: a zero coordinate decomposes to an all-zero block.
* `errorSum_decomposeVec_le`: an error vector against the decomposition of a vector that is
  zero outside one coordinate has magnitude at most `ℓ·β`.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 5.4.3 (gadget `g`, `G = I_n ⊗ gᵗ`, Equation (5.4.1)).
* [GSW13] C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with
  Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, CRYPTO 2013;
  author version dated 8 June 2013, Section 1.3.3 (`BitDecomp`, `Powersof2`) and
  Section 3.2 (`G = BitDecomp⁻¹(I_N)`).
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; ePrint 2014/094 version dated 13 June 2014, Section 3.1 (Equation (3.1)).

**Deviations.** The width `ℓ` is any natural number with `q ≤ 2^ℓ`; [GSW13] fixes
`ℓ = ⌊log₂ q⌋ + 1`, [AP14] and [Pei16] `ℓ = ⌈log₂ q⌉`, and BV14 `⌈log q⌉`. All of these
satisfy the hypothesis. `G⁻¹` is deterministic binary decomposition, as in [GSW13]'s
`BitDecomp`; [AP14, Claim 3.1]'s randomized subgaussian `G⁻¹` uses lattice sampling, which
the campaign plan excludes. The gadget reuses the audited little-endian
`TrapdoorFunctions.Lossy.gadget` and `Randomized.blocksEquiv` rather than a third copy.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

/-- GSW parameters [GSW13, Section 3.1, `Setup`; AP14, Section 3.2]: LWE numeric parameters
(dimension `n`, sample count `m`, modulus `q ≥ 2`) and a gadget width `ℓ` large enough that
every residue has an `ℓ`-bit representative. The noise law is a separate argument, as in
the LWE layer, and the depth `L` is not a field: correctness theorems take it explicitly. -/
structure Parameters where
  /-- The LWE dimension, sample count and modulus. -/
  lwe : LWE.Parameters
  /-- The gadget width `ℓ`: the number of binary digits per residue. -/
  width : ℕ
  /-- Every residue modulo `q` fits in `ℓ` bits. -/
  modulus_le : lwe.modulus ≤ 2 ^ width

/-- The ciphertext width `N = (n+1)·ℓ` [GSW13, Section 3.1; AP14, Section 3.2]. A reducible
abbreviation, so `Fin P.columns` is notation for `Fin ((n+1)*ℓ)`, the index type of the
existing `Lossy.gadget`. -/
abbrev Parameters.columns (P : Parameters) : ℕ := (P.lwe.dimension + 1) * P.width

/-- `P.columns` is `(n+1)·ℓ`. -/
theorem Parameters.columns_eq (P : Parameters) :
    P.columns = (P.lwe.dimension + 1) * P.width := rfl

/-- A GSW ciphertext is an `(n+1) × N` matrix modulo `q` [AP14, Section 3.2, ciphertext space
`C = Z_q^{n × nℓ}`; Pei16, Section 6.1.3]. Reducible notation. -/
abbrev Ciphertext (P : Parameters) : Type :=
  Matrix (Fin (P.lwe.dimension + 1)) (Fin P.columns) (ZMod P.lwe.modulus)

/-- `Ciphertext P` is the type of `(n+1) × N` matrices modulo `q`. -/
theorem Ciphertext_eq (P : Parameters) :
    Ciphertext P = Matrix (Fin (P.lwe.dimension + 1)) (Fin P.columns) (ZMod P.lwe.modulus) :=
  rfl

/-- The gadget matrix `G = I_{n+1} ⊗ gᵗ` modulo `q`: entry `(i, (j,k))` is `2^k` if `i = j`
and `0` otherwise, column `(j,k)` sitting at position `j·ℓ + k` [Pei16, Section 5.4.3;
AP14, Equation (3.1)]. It is the transpose of the audited integer gadget
`Lossy.gadget ℓ (n+1)`, reduced modulo `q`. -/
def gadget (P : Parameters) : Ciphertext P :=
  fun i j => ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
    ZMod P.lwe.modulus)

/-- Entry `(i,j)` of the gadget is the integer gadget's `(j,i)` entry cast modulo `q`. -/
theorem gadget_apply (P : Parameters) (i : Fin (P.lwe.dimension + 1)) (j : Fin P.columns) :
    gadget P i j =
      ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
        ZMod P.lwe.modulus) := rfl

/-- The `ℓ`-bit digit of a residue: its canonical representative in `[0,q)`, which is below
`2^ℓ` by `P.modulus_le` [GSW13, Section 1.3.3, `BitDecomp` of one coordinate]. -/
def digit (P : Parameters) (u : ZMod P.lwe.modulus) : Fin (2 ^ P.width) :=
  ⟨u.val, lt_of_lt_of_le (ZMod.val_lt u) P.modulus_le⟩

/-- The digit of `u` has value `u.val`. -/
theorem digit_val (P : Parameters) (u : ZMod P.lwe.modulus) : (digit P u : ℕ) = u.val := rfl

/-- `G⁻¹` on a vector [Pei16, Equation (5.4.1); GSW13, Section 1.3.3, `BitDecomp`]: the
`N` bits whose block `j` is the little-endian binary expansion of `u j`'s representative.
It is the inverse of the existing block equivalence `Randomized.blocksEquiv (n+1) ℓ`
applied to the digit vector. -/
def decomposeVec (P : Parameters) (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    Fin P.columns → Bool :=
  (Randomized.blocksEquiv (P.lwe.dimension + 1) P.width).symm (fun j => digit P (u j))

/-- `decomposeVec P u` is the inverse block equivalence applied to the digits of `u`. -/
theorem decomposeVec_eq (P : Parameters) (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    decomposeVec P u =
      (Randomized.blocksEquiv (P.lwe.dimension + 1) P.width).symm (fun j => digit P (u j)) :=
  rfl

/-- `G⁻¹` on a matrix, column by column [Pei16, Equation (5.4.1); AP14, Section 3.1,
deterministic specialization]: column `c` of `decompose P M` is `decomposeVec P` of column
`c` of `M`. The column index type is arbitrary. -/
def decompose (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus)) :
    Matrix (Fin P.columns) ι Bool :=
  fun i c => decomposeVec P (fun j => M j c) i

/-- Entry `(i,c)` of `decompose P M` is bit `i` of the decomposition of column `c`. -/
theorem decompose_apply (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus))
    (i : Fin P.columns) (c : ι) :
    decompose P M i c = decomposeVec P (fun j => M j c) i := rfl

/-- Read a Boolean matrix as its `{0,1}` matrix modulo `q`. Technical glue: GSW's short
matrices (`R`, `G⁻¹(·)`) are stored as Booleans so their shortness holds by typing. -/
def lift (P : Parameters) {κ ι : Type*} (X : Matrix κ ι Bool) : Matrix κ ι (ZMod P.lwe.modulus) :=
  fun i j => ((X i j).toNat : ZMod P.lwe.modulus)

/-- Entry `(i,j)` of `lift P X` is `(X i j).toNat` modulo `q`. -/
theorem lift_apply (P : Parameters) {κ ι : Type*} (X : Matrix κ ι Bool) (i : κ) (j : ι) :
    lift P X i j = ((X i j).toNat : ZMod P.lwe.modulus) := rfl

/-- The digit map of the existing gadget recovers the residue digits of `u` from
`decomposeVec P u` [Pei16, Section 5.4.3].

**Proof sketch.** Read `Lossy.digits_eq` and `decomposeVec_eq`; the composite is
`blocksEquiv (blocksEquiv.symm _)`, which `Equiv.apply_symm_apply` reduces to the digits. -/
theorem digits_decomposeVec (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    TrapdoorFunctions.Lossy.digits P.width (P.lwe.dimension + 1) (decomposeVec P u) =
      fun j => digit P (u j) := by
  rw [TrapdoorFunctions.Lossy.digits_eq, decomposeVec_eq, Equiv.apply_symm_apply]

/-- `G · G⁻¹(u) = u` [Pei16, Section 5.4.3, relation `G · G⁻¹(u) = u (mod q)`].

**Proof sketch.** Fix a coordinate `j`. Over the integers, `Lossy.gadget_mulVec` evaluates
`(Lossy.gadget ℓ (n+1))ᵗ · x` at `j`, where `x` is the decomposition read as integers, to the
block-`j` digit, which `digits_decomposeVec` and `digit_val` identify with `(u j).val`. Write
`u j` as the residue of `(u j).val` (`ZMod.natCast_zmod_val`), hence as the residue of that
integer sum; the cast commutes with the finite sum (`Int.cast_sum`), and each term is the
matching entry of `G` times the lifted bit by `gadget_apply` and `Int.cast_mul`. -/
theorem gadget_mulVec_decomposeVec (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    (gadget P).mulVec (fun i => ((decomposeVec P u i).toNat : ZMod P.lwe.modulus)) = u := by
  funext j
  have h := TrapdoorFunctions.Lossy.gadget_mulVec P.width (P.lwe.dimension + 1)
    (decomposeVec P u) j
  simp only [digits_decomposeVec, digit_val] at h
  change (∑ i, TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) i j *
    ((decomposeVec P u i).toNat : ℤ)) = ((u j).val : ℤ) at h
  change ∑ i, gadget P j i * ((decomposeVec P u i).toNat : ZMod P.lwe.modulus) = u j
  rw [← ZMod.natCast_zmod_val (u j), ← Int.cast_natCast (R := ZMod P.lwe.modulus) (u j).val,
    ← h, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gadget_apply, Int.cast_mul, Int.cast_natCast]

/-- `G · G⁻¹(M) = M` for every matrix with `n+1` rows [Pei16, Section 5.4.3; AP14,
Equation (3.1)].

**Proof sketch.** Compare entry `(i, c)`: by `Matrix.mul_apply`, `decompose_apply` and
`lift_apply` it is coordinate `i` of `G` times the lifted decomposition of column `c` of `M`,
which is `M i c` by `gadget_mulVec_decomposeVec`. -/
theorem gadget_mul_decompose (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus)) :
    gadget P * lift P (decompose P M) = M := by
  ext i c
  have h := congrFun (gadget_mulVec_decomposeVec P (fun j => M j c)) i
  rw [Matrix.mul_apply]
  simp only [lift_apply, decompose_apply]
  exact h

/-- A coordinate equal to zero decomposes to an all-false block.

**Proof sketch.** `Lossy.digits_val` writes the block-`j` digit of `decomposeVec P u` as
`∑ₖ bitₖ · 2^k`; by `digits_decomposeVec` and `digit_val` it equals `(u j).val = 0`. A sum of
natural numbers is zero only if every term is (`Finset.sum_eq_zero_iff`), so
`bitₖ · 2^k = 0`; since `2^k ≠ 0`, the bit has value `0`, i.e. it is `false`. -/
theorem decomposeVec_block_eq_false (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (j : Fin (P.lwe.dimension + 1))
    (hj : u j = 0) (k : Fin P.width) :
    decomposeVec P u (finProdFinEquiv (j, k)) = false := by
  have h := TrapdoorFunctions.Lossy.digits_val P.width (P.lwe.dimension + 1) (decomposeVec P u) j
  simp only [digits_decomposeVec, digit_val, hj, ZMod.val_zero] at h
  have hk := (Finset.sum_eq_zero_iff.mp h.symm) k (Finset.mem_univ k)
  rcases Nat.mul_eq_zero.mp hk with hb | hpow
  · exact Bool.toNat_eq_zero.mp hb
  · exact absurd hpow (pow_ne_zero _ two_ne_zero)

/-- If `u` vanishes outside coordinate `j₀`, any error vector with entries bounded by `β`
has inner product with the decomposition of `u` at most `ℓ·β` in absolute value. This is
the decryption-noise bound used for the `G⁻¹`-column decryptor.

**Proof sketch.** Split the sum over `Fin ((n+1)ℓ)` through `finProdFinEquiv` into blocks
(`Equiv.sum_comp`, `Fintype.sum_prod_type`). Every block `j ≠ j₀` vanishes termwise by
`decomposeVec_block_eq_false`, so `Finset.sum_eq_single` leaves block `j₀`. It is a binary
subset sum of `ℓ` errors, each of magnitude at most `β`; apply `LWE.binaryErrorSum_bound`
with `m := ℓ`. -/
theorem errorSum_decomposeVec_le (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (j₀ : Fin (P.lwe.dimension + 1))
    (hu : ∀ j, j ≠ j₀ → u j = 0) (e : Fin P.columns → ℤ) (β : ℕ)
    (he : ∀ i, (e i).natAbs ≤ β) :
    (∑ i, e i * ((decomposeVec P u i).toNat : ℤ)).natAbs ≤ P.width * β := by
  -- Step 1: split the index `Fin ((n+1)ℓ)` into blocks `(j, k)`.
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  -- Step 2: every block other than `j₀` vanishes.
  rw [Finset.sum_eq_single j₀ (fun j _ hj => Finset.sum_eq_zero fun k _ => by
      rw [decomposeVec_block_eq_false P u j (hu j hj) k, Bool.toNat_false, Nat.cast_zero,
        mul_zero])
    (fun h => absurd (Finset.mem_univ j₀) h)]
  -- Step 3: the surviving block is a binary subset sum of `ℓ` bounded errors.
  exact LWE.binaryErrorSum_bound (fun k => e (finProdFinEquiv (j₀, k)))
    (fun k => decomposeVec P u (finProdFinEquiv (j₀, k))) β fun k => he _

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW


run_cmd do
  let label := "cp1_TCSlib_Cryptography_AdvancedEncryption_Homomorphic_GSW_Gadget_B_coe"
  Lean.logInfo m!"GSWCORE-EOF {label}"
