/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "final_TCSlib_Cryptography_Hashing_SIS_Columns_B_coe"
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
# Leftover hashing of many independent columns under one public matrix

## Main definitions

* `hashColumns`: hash `N` independent binary columns with the same matrix, `A ↦ A R`.

## Main results

* `distAdv_hashColumns_uniform_le`: `(A, A R)` is within `N` times the single-column
  leftover-hash error of `(A, U)` with `U` uniform.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 5.2.1 (leftover hashing in Regev encryption) and Section 6.1.3
  ("`[Ā | ĀR]` is very close to uniformly distributed").
* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013,
  Section 3.2, Lemma 1 (`(A, R·A)` close to uniform).
* [Vad12] S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18.

The bound is a column-by-column hybrid over the existing single-column
`distAdv_hash_uniform_le`. It is not a matrix leftover-hash lemma: the family `R ↦ A R` is not
universal on whole matrices, and no such claim is made. No SIS hardness is used.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open TCSlib.Cryptography.SIS (Parameters)

/-- Hash `N` binary columns with one matrix: column `j` of `hashColumns P N A R` is
`hash P A (R · j)`, so `hashColumns P N A R = A R` modulo `q` [Pei16, Section 6.1.3, `ĀR`]. -/
def hashColumns (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) :
    Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus) :=
  fun i j => hash P A (fun c => R c j) i

/-- Entry `(i,j)` of `hashColumns P N A R` is coordinate `i` of the hash of column `j`. -/
theorem hashColumns_apply (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) (i : Fin P.dimension) (j : Fin N) :
    hashColumns P N A R i j = hash P A (fun c => R c j) i := rfl

/-- `hashColumns` is matrix multiplication by the `{0,1}` lift of `R`.

**Proof sketch.** Entrywise: by `hashColumns_apply`, `hash_eq` and `Matrix.mul_apply'` both
sides are the same dot product of row `i` of `A` with the lifted column `j` of `R`. -/
theorem hashColumns_eq_mul (P : Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) :
    hashColumns P N A R = A * Matrix.of fun c j => ((R c j).toNat : ZMod P.modulus) := by
  ext i j
  rw [hashColumns_apply, hash_eq, Matrix.mul_apply']
  rfl

/-- **Column hybrid for leftover hashing** [GSW13, Section 3.2, Lemma 1, statistical half;
Pei16, Section 6.1.3]: any independently randomized test distinguishes `(A, A R)` from a
uniform `(A, U)`, for uniform `A` and uniform binary `R` with `N` columns, with advantage at
most `N` times the single-column error `½·√(q^{dimension}/2^{columns})`.

**Proof sketch.** Hybrid `H_k`, on seeds `(A, (x, u))` with binary columns `x j` and uniform
columns `u j`: column `j` of the second component is `u j` for `j < k` and `hash A (x j)`
otherwise, all under the same `A`. The `k`-th test plants its challenge column at `k`,
simulates the other columns from coins `(x, u)` carried beside `D`'s own coins (a product of
finite nonempty types), and runs `D`. By `acceptProb_bind`, a seed relabelling
(`acceptProb_comp_equiv`) and `acceptProb_update`, it accepts `(A, hash A r)` exactly as `D`
accepts `H_k`, and a uniform `(A, y)` exactly as `D` accepts `H_{k+1}`. `H_0` is the real
sampler and `H_N` the ideal one after transposing the seeds and dropping the unused columns
(`acceptProb_comp_equiv`, `acceptProb_fst`). `abs_sub_le_sum_hybrids` bounds the end-to-end
gap by the `N` neighbouring gaps, each at most the single-column error by
`distAdv_hash_uniform_le`. At `N = 0` the sum is empty. -/
theorem distAdv_hashColumns_uniform_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (N : ℕ)
    (D : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.columns) (Fin N) Bool => (r.1, hashColumns P N r.1 r.2))
      (id : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)) → _) D ≤
      N * ((1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns)) := by
  classical
  let Key := Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)
  let In := Fin P.columns → Bool
  let Out := Fin P.dimension → ZMod P.modulus
  let Mat := Matrix (Fin P.dimension) (Fin N) (ZMod P.modulus)
  let Cols := (Fin N → In) × (Fin N → Out)
  -- Hybrid `k`: columns `j < k` are uniform, the others hash binary columns under `A`.
  let hyb (k : ℕ) (s : Key × Cols) : Key × Mat :=
    (s.1, Matrix.of fun i j => if (j : ℕ) < k then s.2.2 j i else hash P s.1 (s.2.1 j) i)
  -- The `k`-th test plants its challenge at column `k` and simulates the other columns.
  let plant (k : ℕ) (z : Key × Out) (c : Cols) : Key × Mat :=
    (z.1, Matrix.of fun i j => if (j : ℕ) < k then c.2 j i else if (j : ℕ) = k then z.2 i
      else hash P z.1 (c.1 j) i)
  let test (k : ℕ) (z : Key × Out) (c : Cols × ρ) : Bool := D (plant k z c.1) c.2
  -- Step 1: on a real challenge, the `k`-th test runs `D` on hybrid `k`.
  have hleft (k : ℕ) (hk : k < N) :
      acceptProb (fun r : Key × In => (r.1, hash P r.1 r.2)) (test k) =
        acceptProb (hyb k) D := by
    let e : (Key × In) × Cols ≃ In × ((Fin N → In) × (Key × (Fin N → Out))) :=
      ⟨fun w => (w.1.2, (w.2.1, (w.1.1, w.2.2))), fun v => ((v.2.2.1, v.1), (v.2.1, v.2.2.2)),
        fun _ => rfl, fun _ => rfl⟩
    let e' : (Fin N → In) × (Key × (Fin N → Out)) ≃ Key × Cols :=
      ⟨fun v => (v.2.1, (v.1, v.2.2)), fun s => (s.2.1, (s.1, s.2.2)), fun _ => rfl, fun _ => rfl⟩
    refine (acceptProb_bind _ (plant k) D).trans (Eq.trans ?_
      ((acceptProb_comp_equiv e
        (fun w => hyb k (e' (Function.update w.2.1 ⟨k, hk⟩ w.1, w.2.2))) D).trans
      ((acceptProb_update (ρ := ρ) (⟨k, hk⟩ : Fin N) (fun c v => hyb k (e' (c, v))) D).trans
        (acceptProb_comp_equiv e' (hyb k) D))))
    refine congrArg (fun X => acceptProb X D) ?_
    funext w
    refine Prod.ext rfl ?_
    ext i j
    simp only [plant, hyb, e, e', Equiv.coe_fn_mk, Matrix.of_apply]
    by_cases hj : (j : ℕ) = k
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
      simp only [lt_irrefl, if_false, if_true, Function.update_self]
    · have hne : j ≠ ⟨k, hk⟩ := fun h => hj (congrArg Fin.val h)
      simp only [hj, if_false, Function.update_of_ne hne]
  -- Step 2: on a uniform challenge, the `k`-th test runs `D` on hybrid `k + 1`.
  have hright (k : ℕ) (hk : k < N) :
      acceptProb (id : Key × Out → Key × Out) (test k) = acceptProb (hyb (k + 1)) D := by
    let e : (Key × Out) × Cols ≃ Out × ((Fin N → Out) × (Key × (Fin N → In))) :=
      ⟨fun w => (w.1.2, (w.2.2, (w.1.1, w.2.1))), fun v => ((v.2.2.1, v.1), (v.2.2.2, v.2.1)),
        fun _ => rfl, fun _ => rfl⟩
    let e' : (Fin N → Out) × (Key × (Fin N → In)) ≃ Key × Cols :=
      ⟨fun v => (v.2.1, (v.2.2, v.1)), fun s => (s.2.2, (s.1, s.2.1)), fun _ => rfl, fun _ => rfl⟩
    refine (acceptProb_bind _ (plant k) D).trans (Eq.trans ?_
      ((acceptProb_comp_equiv e
        (fun w => hyb (k + 1) (e' (Function.update w.2.1 ⟨k, hk⟩ w.1, w.2.2))) D).trans
      ((acceptProb_update (ρ := ρ) (⟨k, hk⟩ : Fin N) (fun c v => hyb (k + 1) (e' (c, v))) D).trans
        (acceptProb_comp_equiv e' (hyb (k + 1)) D))))
    refine congrArg (fun X => acceptProb X D) ?_
    funext w
    refine Prod.ext rfl ?_
    ext i j
    simp only [plant, hyb, e, e', Equiv.coe_fn_mk, Matrix.of_apply, id_eq]
    rcases lt_trichotomy (j : ℕ) k with h | h | h
    · have hne : j ≠ ⟨k, hk⟩ := fun h' => h.ne (congrArg Fin.val h')
      simp only [h, Nat.lt_succ_of_lt h, if_true, Function.update_of_ne hne]
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext h
      simp only [lt_irrefl, Nat.lt_succ_self, if_false, if_true, Function.update_self]
    · have hne : j ≠ ⟨k, hk⟩ := fun h' => h.ne' (congrArg Fin.val h')
      simp only [not_lt.mpr h.le, not_lt.mpr (Nat.succ_le_of_lt h), h.ne', if_false]
  -- Step 3: hybrid `0` is the real sampler and hybrid `N` the ideal one, after relabelling.
  have hzero : acceptProb (fun r : Key × Matrix (Fin P.columns) (Fin N) Bool =>
      (r.1, hashColumns P N r.1 r.2)) D = acceptProb (hyb 0) D := by
    let e : Key × Cols ≃ (Key × Matrix (Fin P.columns) (Fin N) Bool) × (Fin N → Out) :=
      ⟨fun s => ((s.1, fun c j => s.2.1 j c), s.2.2), fun t => (t.1.1, (fun j c => t.1.2 c j, t.2)),
        fun _ => rfl, fun _ => rfl⟩
    refine (acceptProb_fst (τ := Fin N → Out) _ D).symm.trans (Eq.trans
      (acceptProb_comp_equiv e (fun t => (t.1.1, hashColumns P N t.1.1 t.1.2)) D).symm ?_)
    refine congrArg (fun X => acceptProb X D) ?_
    funext s
    refine Prod.ext rfl ?_
    ext i j
    simp only [hyb, e, Equiv.coe_fn_mk, Matrix.of_apply, hashColumns_apply, Nat.not_lt_zero,
      if_false]
  have hfull : acceptProb (id : Key × Mat → Key × Mat) D = acceptProb (hyb N) D := by
    let e : Key × Cols ≃ (Key × Mat) × (Fin N → In) :=
      ⟨fun s => ((s.1, Matrix.of fun i j => s.2.2 j i), s.2.1),
        fun t => (t.1.1, (t.2, fun j i => t.1.2 i j)), fun _ => rfl, fun _ => rfl⟩
    refine (acceptProb_fst (τ := Fin N → In) _ D).symm.trans (Eq.trans
      (acceptProb_comp_equiv e (fun t => id t.1) D).symm ?_)
    refine congrArg (fun X => acceptProb X D) ?_
    funext s
    refine Prod.ext rfl ?_
    ext i j
    simp only [hyb, e, Equiv.coe_fn_mk, Matrix.of_apply, id_eq, j.isLt, if_true]
  -- Step 4: telescope the neighbouring gaps and bound each by the single-column lemma.
  have hgap (k : ℕ) (hk : k ∈ Finset.range N) :
      |acceptProb (hyb k) D - acceptProb (hyb (k + 1)) D| ≤
        (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) := by
    have h := distAdv_hash_uniform_le P (test k)
    rwa [distAdv_def, hleft k (Finset.mem_range.1 hk), hright k (Finset.mem_range.1 hk)] at h
  rw [distAdv_def, hzero, hfull]
  refine (abs_sub_le_sum_hybrids (fun k => acceptProb (hyb k) D) N).trans
    ((Finset.sum_le_sum hgap).trans_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end TCSlib.Cryptography.Hashing.SIS


run_cmd do
  let label := "final_TCSlib_Cryptography_Hashing_SIS_Columns_B_coe"
  Lean.logInfo m!"GSWSEC-EOF {label}"
