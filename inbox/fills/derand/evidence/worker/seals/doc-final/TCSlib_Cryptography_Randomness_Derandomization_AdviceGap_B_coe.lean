/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "doc-final_TCSlib_Cryptography_Randomness_Derandomization_AdviceGap_B_coe"
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
    Lean.logInfo m!"DERAND-CATALOG {label} {row.compress}"
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
    unless installed == .irreducible do throwError "DERAND seal installation failed: {name}"
  let maskExt := Lean.Meta.globalInstanceExtension
  let maskEnv ← Lean.getEnv
  let scopes := maskExt.ext.getState maskEnv
  unless scopes.stateStack.length == 1 do throwError "DERAND seal requires base scope"
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
    if scopedNames.contains name then throwError "DERAND scoped instance overlap: {name}"
  Lean.modifyEnv fun current =>
    maskExt.modifyState current fun membership =>
      requested.foldl (fun state name => state.erase name) membership
  let maskedEnv ← Lean.getEnv
  unless beforeLookup == lookupSnapshot maskedEnv do
    throwError "DERAND typeclass lookup changed"
  for name in requested do
    if Lean.Meta.isGlobalInstance maskedEnv name then
      throwError "DERAND instance unfolding mask failed: {name}"
  Lean.logInfo m!"DERAND-INSTALL {label} requested={requested.size} active={active} already={already} excluded={excluded} tc_state=preserved"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A non-uniform advice bound for verifier gaps

The bad input in [PS10, Theorem 180.1] is advice for a distinguisher. A
polynomial bound on its length in the seed parameter suffices to rule out
every large-parameter gap, including when several input lengths share that
parameter. No computable choice of advice is required by non-uniform security.

## Main results

* `TCSlib.Cryptography.Randomness.Derand.eff_mapCoins`: efficient coin reindexing.
* `TCSlib.Cryptography.Randomness.Derand.exists_verifier_gap_bound`: a uniform
  constant bound on the verifier's PRG gap beyond a seed threshold.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, §8.2, Theorem 180.1.
-/

namespace TCSlib.Cryptography.Randomness.Derand

open Complexity Turing

/-- An efficient Boolean verifier remains efficient after an FP coin map:
if `C` is FP on encoded pairs, then `(x,r) ↦ M x (C ⟨x,r⟩)` is efficient.
This is `P`-preimage closure for the existing true and false languages.
[PS10, §8.2, Theorem 180.1]

**Proof sketch.** Extract the verifier's two `P` languages with the published
efficiency reader. Take their preimages under `z ↦ ⟨fst z,C z⟩`, which is FP
by pairing. The Boolean-verifier and pair-projection readers identify the
resulting true and false events on every encoded pair. -/
theorem eff_mapCoins {M : List Bool → List Bool → Bool}
    (hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M))
    {C : List Bool → List Bool} (hC : PolyTimeComputable C) :
    Randomized.polyTimeModel.Eff
      (Randomized.boolVerifier fun x r => M x (C (pairEncode x r))) := by
  obtain ⟨V₁, V₀, h₁, h₀, hV⟩ :=
    (Randomized.polyTimeModel_eff_iff (Randomized.boolVerifier M)).mp hM
  let f : List Bool → List Bool := fun z => pairEncode (pairFstD z) (C z)
  have hf : PolyTimeComputable f := polyTimeComputable_pairFstD.pairEncode hC
  refine (Randomized.polyTimeModel_eff_iff _).mpr
    ⟨f ⁻¹' V₁, f ⁻¹' V₀, preimage_mem_P h₁ hf, preimage_mem_P h₀ hf, ?_⟩
  intro x r
  change
    (Randomized.boolVerifier (fun x r => M x (C (pairEncode x r))) x r = some true ↔
      f (pairEncode x r) ∈ V₁) ∧
    (Randomized.boolVerifier (fun x r => M x (C (pairEncode x r))) x r = some false ↔
      f (pairEncode x r) ∈ V₀)
  simpa only [Randomized.boolVerifier_apply, f, pairFstD_pairEncode]
    using hV x (C (pairEncode x r))

/-- For a secure PRG, any efficient Boolean verifier has gap at most `1/12`
on every input whose seed parameter is sufficiently large, provided the input
length is polynomial in that parameter:
`|Pr[M(x;G(U_s))=1] - Pr[M(x;U_stretch(s))=1]| ≤ 1/12` for `s = w |x| ≥ S`.
[PS10, §8.2, Theorem 180.1]

**Proof sketch.** At each seed length with a gap above `1/12`, choose one bad
input as advice. Else use the empty word. The hypothesis bounds this advice
by `p`, so `verifier_toNUPPT` gives one non-uniform distinguisher for all seed
lengths. Its advantage is exactly the selected gap: use the published PRG,
acceptance-probability and distinguisher readers, then `uprob_fst` to remove
the unused coins. Security bounds that advantage by `1/s` eventually, which
is at most `1/12` for `s ≥ 12`. Hence no such bad input exists beyond the
maximum of these two thresholds. -/
theorem exists_verifier_gap_bound {M : List Bool → List Bool → Bool}
    (hM : Randomized.polyTimeModel.Eff (Randomized.boolVerifier M))
    (w : ℕ → ℕ) (p : PolyExpr) (hsize : ∀ n, n ≤ p.eval (w n))
    (G : PRG) (hG : G.Secure) :
    ∃ S : ℕ, ∀ x : List Bool, S ≤ w x.length →
      |uprob (fun r : Fin (w x.length) → Bool =>
          M x (List.ofFn (G.G (w x.length) r)) = true) -
        uprob (fun r : Fin (G.stretch.eval (w x.length)) → Bool =>
          M x (List.ofFn r) = true)| ≤ (1 : ℝ) / 12 := by
  classical
  let gap (x : List Bool) (s : ℕ) : ℝ :=
    |uprob (fun r : Fin s → Bool => M x (List.ofFn (G.G s r)) = true) -
      uprob (fun r : Fin (G.stretch.eval s) → Bool => M x (List.ofFn r) = true)|
  let bad (s : ℕ) : Prop := ∃ x : List Bool, w x.length = s ∧ (1 : ℝ) / 12 < gap x s
  let xs (s : ℕ) : List Bool := if h : bad s then Classical.choose h else []
  have hselected (s : ℕ) (hs : bad s) :
      w (xs s).length = s ∧ (1 : ℝ) / 12 < gap (xs s) s := by
    dsimp only [xs]
    rw [dif_pos hs]
    exact Classical.choose_spec hs
  have hxs (s : ℕ) : (xs s).length ≤ p.eval s := by
    by_cases hs : bad s
    · have h := hsize (xs s).length
      rw [(hselected s hs).1] at h
      exact h
    · simp only [xs, dif_neg hs, List.length_nil]
      exact Nat.zero_le _
  obtain ⟨D, _, hD⟩ := verifier_toNUPPT hM xs p hxs
  have hadv (s : ℕ) :
      prgAdv (G.G s) (D.distinguisher s (G.stretch.eval s)) = gap (xs s) s := by
    rw [prgAdv_eq, distAdv_def]
    dsimp only [gap]
    congr 1
    congr 1
    · rw [acceptProb_def]
      simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, hD,
        List.cons.injEq, and_true, decide_eq_true_eq]
      exact uprob_fst (α := Fin s → Bool) (β := D.Coins s)
        (fun r => M (xs s) (List.ofFn (G.G s r)) = true)
    · rw [acceptProb_def]
      simp only [id_eq, NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq, hD,
        List.cons.injEq, and_true, decide_eq_true_eq]
      exact uprob_fst (α := Fin (G.stretch.eval s) → Bool) (β := D.Coins s)
        (fun r => M (xs s) (List.ofFn r) = true)
  have hneg := ((PRG.secure_iff G).mp hG).2 D
  obtain ⟨N, hN⟩ := (negligible_iff _).mp hneg 1
  refine ⟨max N 12, fun x hx => ?_⟩
  change gap x (w x.length) ≤ (1 : ℝ) / 12
  by_contra hgap
  have hb : bad (w x.length) := ⟨x, rfl, lt_of_not_ge hgap⟩
  have hlow := (hselected (w x.length) hb).2
  have hhigh := hN (w x.length) ((le_max_left N 12).trans hx)
  rw [hadv, abs_of_nonneg (abs_nonneg _), pow_one] at hhigh
  have hs : (12 : ℝ) ≤ (w x.length : ℝ) := by
    exact_mod_cast (le_max_right N 12).trans hx
  have hinv : 1 / (w x.length : ℝ) ≤ (1 : ℝ) / 12 :=
    one_div_le_one_div_of_le (by norm_num) hs
  linarith

end TCSlib.Cryptography.Randomness.Derand


run_cmd do
  let label := "doc-final_TCSlib_Cryptography_Randomness_Derandomization_AdviceGap_B_coe"
  Lean.logInfo m!"DERAND-EOF {label}"
