/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Hybrid
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridMessage
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
            (true && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit-transfer answers as active wire labels

The bit-transfer functionality returns one bit to the receiver in every call. Its
concatenated answer word can therefore be identified from a product-indexed bit reader.
The relabeled seed turns the selected input-wire labels into the false labels.

## Main definitions

There are no new definitions.

## Main results

* `length_answersB`: one receiver bit per call gives the exact answer-word length.
* `answersB_eq_active`: the product-indexed key reader identifies the active-key word.
* `answersA_nil`: the sender receives an empty answer word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 (one bit transfer for every key bit).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords

open Complexity Turing BoolCircuit

/-- Bob's concatenated answers to bit transfer have exactly one bit per call:
`(H.answersB n xs ys rA rB).length = H.calls.eval n`. [PS10, Protocol 162.6] -/
theorem length_answersB (H : HybridProtocol otFunctionality) (n : ℕ)
    (xs ys rA rB : List Bool) :
    (H.answersB n xs ys rA rB).length = H.calls.eval n := by
  rw [HybridProtocol.answersB_eq, List.length_flatten, List.map_ofFn]
  change (List.ofFn (fun j : Fin (H.calls.eval n) =>
    (List.ofFn (otFunctionality.f n (H.callA n xs rA j) (H.callB n ys rB j)).2).length)).sum = _
  simp only [List.length_ofFn, otFunctionality_outB, PolyExpr.eval_const,
    List.ofFn_const, List.sum_replicate_nat, Nat.mul_one]

/-- Suppose `count * width` bit-transfer calls return the key bits read at `(i,t)`, and
the chosen wire values agree with Bob's input word. The full receiver answer word is then
the false-key word under the relabeled seed. No positive-width assumption is required.
[PS10, Protocol 162.6]

**Proof sketch.** One bit per call gives the exact total length. Every valid flat index
comes from the finite product of a wire and a key-bit index. At this index, the supplied
answer reader and the public seed-relabeling reader give the same bit. List extensionality
then identifies the complete words. -/
theorem answersB_eq_active {m width : ℕ} {ρ : Type}
    (H : HybridProtocol otFunctionality) (n : ℕ) (xs ys rA rB : List Bool)
    (C : DAGCircuit m) (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ)
    (v : ℕ → Bool) (hCalls : H.calls.eval n = count * width)
    (hv : ∀ i : Fin count, v (first + i) = ys.getD i false)
    (hpoint : ∀ (i : Fin count) (t : Fin width),
      (H.answersB n xs ys rA rB).getD (i * width + t) false =
        keyAt C s (first + i) (ys.getD i false) t) :
    H.answersB n xs ys rA rB =
      List.ofFn (FakeObjects.activeAnswers C (RelabelGarbling.relabelSeed C v s) first count) := by
  have hlen := (length_answersB H n xs ys rA rB).trans hCalls
  have hBit (j : Fin (count * width)) :
      (H.answersB n xs ys rA rB).getD j false =
        FakeObjects.activeAnswers C (RelabelGarbling.relabelSeed C v s) first count j := by
    obtain ⟨⟨i, t⟩, rfl⟩ := (finProdFinEquiv (m := count) (n := width)).surjective j
    rw [GateHybridMessage.activeAnswers_relabel]
    change _ = keyAt C s (first + (finProdFinEquiv.symm (finProdFinEquiv (i, t))).1)
      (v (first + (finProdFinEquiv.symm (finProdFinEquiv (i, t))).1))
      (finProdFinEquiv.symm (finProdFinEquiv (i, t))).2
    rw [Equiv.symm_apply_apply, hv]
    have hi : i * width + t = (finProdFinEquiv (i, t) : ℕ) := by
      rw [finProdFinEquiv_apply_val]
      ring
    rw [← hi, hpoint]
  apply List.ext_getElem
  · rw [List.length_ofFn]
    exact hlen
  · intro i hi hj
    have h := hBit ⟨i, by omega⟩
    simpa only [List.getD_eq_getElem _ _ hi, List.getElem_ofFn] using h

/-- The sender receives no bits from any number of ideal bit transfers:
`H.answersA n xs ys rA rB = []`. [PS10, Protocol 162.6] -/
theorem answersA_nil (H : HybridProtocol otFunctionality) (n : ℕ)
    (xs ys rA rB : List Bool) : H.answersA n xs ys rA rB = [] := by
  rw [HybridProtocol.answersA_eq]
  apply List.flatten_eq_nil_iff.mpr
  intro word hw
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
  apply List.eq_nil_of_length_eq_zero
  simp only [List.length_ofFn, otFunctionality_outA, PolyExpr.eval_const]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.OTAnswerWords
