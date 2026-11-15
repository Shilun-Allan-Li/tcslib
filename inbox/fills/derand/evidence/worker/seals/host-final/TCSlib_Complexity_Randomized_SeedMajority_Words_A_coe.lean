/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.RandomBits
import TCSlib.Complexity.SpaceComplexity.Codec.Word
import TCSlib.Complexity.ClassP.BinaryArith.Unary
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 65536
run_cmd do
  let env ← Lean.getEnv
  let label := "host-final_TCSlib_Complexity_Randomized_SeedMajority_Words_A_coe"
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
# Binary seed words for the majority host

The rank encoding and finite prefix count used by the counting enumeration host H17.
The existing `Randomized.bitsEquiv` identifies ranks with fixed-width Boolean tuples;
the configuration codec's binary normalization lemma identifies its inverse with the
word computed by padding and prefix truncation.

## Main definitions

* `Complexity.SeedMajority.word`: the width-`m` low bits of a natural rank.

## Main results

* `Complexity.SeedMajority.length_word`: every encoded seed has exactly its width.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §7.1, p. 126.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, §8.2, Theorem 180.1.
-/

namespace Complexity.SeedMajority

open Turing

/-- The width-`m` seed word for rank `i` is the first `m` bits of `Nat.bits i`
followed by the binary word for `2 ^ m`, whose first `m` letters are zero:
`word m i = (Nat.bits i ++ Nat.bits (2 ^ m)).take m`.
[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4] -/
def word (m i : ℕ) : List Bool := (Nat.bits i ++ Nat.bits (2 ^ m)).take m

/-- The rank encoder satisfies
`word m i = (Nat.bits i ++ Nat.bits (2 ^ m)).take m`. -/
theorem word_eq (m i : ℕ) :
    word m i = (Nat.bits i ++ Nat.bits (2 ^ m)).take m := rfl

/-- The rank encoder has its declared width: `(word m i).length = m`. -/
theorem length_word (m i : ℕ) : (word m i).length = m := by
  rw [word_eq, bits_two_pow_eq_replicate, List.length_take, List.length_append,
    List.length_append, List.length_replicate, List.length_singleton]
  exact Nat.min_eq_left (by omega)

/-- For `i < 2 ^ m`, `word m i` is the tuple of the existing rank bijection:
`word m i = List.ofFn ((Randomized.bitsEquiv m).symm ⟨i, hi⟩)`.

**Proof sketch.** Decode the inverse tuple with `bitsEquiv_apply`. Its value is `i`
and its length is `m`. The codec's normalization theorem therefore writes it as
`Nat.bits i` padded by exactly `m - |Nat.bits i|` zeros. Taking `m` letters of
`Nat.bits i` followed by `m` zeros gives this same word, since `i < 2 ^ m` bounds
the normalized binary length by `m`. -/
theorem word_eq_ofFn (m i : ℕ) (hi : i < 2 ^ m) :
    word m i = List.ofFn ((Randomized.bitsEquiv m).symm ⟨i, hi⟩) := by
  let u := (Randomized.bitsEquiv m).symm ⟨i, hi⟩
  have hv : LogProg.bitsVal (List.ofFn u) = i := by
    rw [← Randomized.bitsEquiv_apply]
    exact congrArg Fin.val ((Randomized.bitsEquiv m).apply_symm_apply ⟨i, hi⟩)
  have hnorm := Codec.eq_bits_append_replicate (List.ofFn u)
  rw [hv, List.length_ofFn] at hnorm
  have hlen := LogProg.length_bits_le hi
  calc
    word m i = Nat.bits i ++ List.replicate (m - (Nat.bits i).length) false := by
      rw [word_eq, List.take_append, List.take_of_length_le hlen,
        bits_two_pow_eq_replicate,
        List.take_append_of_le_length (by simp),
        List.take_replicate,
        Nat.min_eq_left (Nat.sub_le m _)]
    _ = List.ofFn u := hnorm.symm

open Classical in
/-- The prefix acceptance count is
`count V x m i = #{j ∈ Finset.range i | pairEncode x (word m j) ∈ V}`.
[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4] -/
noncomputable def count (V : Language Bool) (x : List Bool) (m i : ℕ) : ℕ :=
  (Finset.range i |>.filter fun j => pairEncode x (word m j) ∈ V).card

open Classical in
/-- The prefix count satisfies
`count V x m i = #{j ∈ Finset.range i | pairEncode x (word m j) ∈ V}`. -/
theorem count_eq (V : Language Bool) (x : List Bool) (m i : ℕ) :
    count V x m i = (Finset.range i |>.filter fun j => pairEncode x (word m j) ∈ V).card :=
  rfl

/-- The empty prefix has no accepted ranks: `count V x m 0 = 0`. -/
theorem count_zero (V : Language Bool) (x : List Bool) (m : ℕ) : count V x m 0 = 0 := by
  classical
  rw [count_eq]
  simp

/-- At most `i` ranks are accepted in the first `i` tests: `count V x m i ≤ i`. -/
theorem count_le (V : Language Bool) (x : List Bool) (m i : ℕ) : count V x m i ≤ i := by
  classical
  rw [count_eq]
  calc
    _ ≤ (Finset.range i).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = i := Finset.card_range i

open Classical in
/-- One more seed increases the prefix count by its acceptance bit:
`count V x m (i + 1) = count V x m i + if pairEncode x (word m i) ∈ V then 1 else 0`.
[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4] -/
theorem count_succ (V : Language Bool) (x : List Bool) (m i : ℕ) :
    count V x m (i + 1) =
      count V x m i + if pairEncode x (word m i) ∈ V then 1 else 0 := by
  rw [count_eq, count_eq, Finset.range_add_one, Finset.filter_insert]
  by_cases h : pairEncode x (word m i) ∈ V
  · have hnot : i ∉ (Finset.range i).filter (fun j => pairEncode x (word m j) ∈ V) := by
      intro hi
      exact (Nat.lt_irrefl i) (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    rw [if_pos h, if_pos h, Finset.card_insert_of_notMem hnot]
  · rw [if_neg h, if_neg h, Nat.add_zero]

open Classical in
/-- Counting every rank is counting every width-`m` Boolean tuple:
`count V x m (2 ^ m) = #{u : Fin m → Bool | pairEncode x (List.ofFn u) ∈ V}`.
[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4]

**Proof sketch.** Map an accepted rank to the inverse of `Randomized.bitsEquiv`.
`word_eq_ofFn` preserves its test result. Injectivity follows by applying that
equivalence, and every accepted tuple has its rank as a preimage. -/
theorem count_all (V : Language Bool) (x : List Bool) (m : ℕ) :
    count V x m (2 ^ m) =
      (Finset.univ.filter fun u : Fin m → Bool => pairEncode x (List.ofFn u) ∈ V).card := by
  rw [count_eq]
  refine Finset.card_bij (fun i hi => (Randomized.bitsEquiv m).symm
    ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩) ?_ ?_ ?_
  · intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← word_eq_ofFn m i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)]
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    have := congrArg (fun u => ((Randomized.bitsEquiv m) u).val) hij
    simpa only [Equiv.apply_symm_apply] using this
  · intro u hu
    let i := ((Randomized.bitsEquiv m) u).val
    have hi : i < 2 ^ m := ((Randomized.bitsEquiv m) u).isLt
    have hiFin : (⟨i, hi⟩ : Fin (2 ^ m)) = (Randomized.bitsEquiv m) u := by
      apply Fin.ext
      rfl
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ?_⟩, ?_⟩
    · rw [word_eq_ofFn m i hi, hiFin, Equiv.symm_apply_apply]
      exact (Finset.mem_filter.mp hu).2
    · exact (congrArg (Randomized.bitsEquiv m).symm hiFin).trans
        ((Randomized.bitsEquiv m).symm_apply_apply u)

/-- The state word stores the input, binary rank, and binary acceptance count:
`state x i a = pairEncode x (pairEncode (Nat.bits i) (Nat.bits a))`.
[AB09, §7.1, p. 126]; [PS10, §8.2, Theorem 180.1, step 4] -/
def state (x : List Bool) (i a : ℕ) : List Bool :=
  pairEncode x (pairEncode (Nat.bits i) (Nat.bits a))

/-- The state encoder satisfies
`state x i a = pairEncode x (pairEncode (Nat.bits i) (Nat.bits a))`. -/
theorem state_eq (x : List Bool) (i a : ℕ) :
    state x i a = pairEncode x (pairEncode (Nat.bits i) (Nat.bits a)) := rfl

end Complexity.SeedMajority


run_cmd do
  let label := "host-final_TCSlib_Complexity_Randomized_SeedMajority_Words_A_coe"
  Lean.logInfo m!"DERAND-EOF {label}"
