/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Sigma
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedStep
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedAdviceBounds
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
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
            (false && coe && projection)
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
# Finite advice choices for all selected hybrid substeps

A choice stores an optional input and actual gate argument, together with the complete
baseline tape. The absent choice keeps the type nonempty even for an empty circuit. All
slice messages and advice are fixed before the challenge key and nonces are supplied.

## Main definitions

* `Selection`, `wire`: an actual argument and its vertex.
* `Tape`, `Choice`: baseline tape and the finite padded advice-option family.
* `rows`: the canonical complete assignment enumeration.
* `offset`, `len`, `message`, `advice`: fixed finite-choice reduction data.

## Main results

* Exact public readers, slice-fit and polynomial-advice bounds.
* `rebuild_some`: both actual filled-seed sampler endpoints at every real choice.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (fixing inputs, the selected step and all other coins).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices

open Complexity Turing BoolCircuit TCSlib.Cryptography

/-- A selection is a gate and one of its actual argument positions. -/
abbrev Selection {m : ℕ} (C : DAGCircuit m) :=
  Σ i : Fin C.gates.length, Fin C.gates[i.val].args.length

/-- `Selection C` is the dependent pair of a gate index and a valid argument index. -/
theorem Selection_eq {m : ℕ} (C : DAGCircuit m) :
    Selection C = (Σ i : Fin C.gates.length, Fin C.gates[i.val].args.length) := rfl

/-- The selected vertex is the vertex read at the selected argument position. Acyclicity
puts this vertex within the circuit's finite key table. -/
def wire {m : ℕ} (C : DAGCircuit m) (a : Selection C) : Fin C.size :=
  ⟨C.gates[a.1.val].args[a.2.val], by
    have h := GateOccurrences.selected_wire_lt C a.1 _ (List.getElem_mem a.2.isLt)
    have hi := a.1.isLt
    rw [DAGCircuit.size_eq]
    omega⟩

/-- `wire C a` has value `C.gates[a.gate].args[a.position]`. -/
theorem wire_val {m : ℕ} (C : DAGCircuit m) (a : Selection C) :
    (wire C a).val = C.gates[a.1.val].args[a.2.val] := rfl

/-- The full baseline tape has `10*S(n)*n+2*S(n)` bits, including all unused coordinates. -/
abbrev Tape (S : PolyExpr) (n : ℕ) := Fin (10 * S.eval n * n + 2 * S.eval n) → Bool

/-- `Tape S n` is the complete addressed key/nonce/shift bit-vector type. -/
theorem Tape_eq (S : PolyExpr) (n : ℕ) :
    Tape S n = (Fin (10 * S.eval n * n + 2 * S.eval n) → Bool) := rfl

/-- A choice is an optional input and actual selected argument, paired with a full baseline
tape. `none` permits an advice choice even when no gate or input option exists. -/
abbrev Choice (I : ℕ → Type) {inputs : ℕ → ℕ} (C : ∀ n, DAGCircuit (inputs n))
    (S : PolyExpr) (n : ℕ) := Option (I n × Selection (C n)) × Tape S n

/-- `Choice I C S n` retains an optional input/argument pair and the full baseline tape. -/
theorem Choice_eq (I : ℕ → Type) {inputs : ℕ → ℕ} (C : ∀ n, DAGCircuit (inputs n))
    (S : PolyExpr) (n : ℕ) :
    Choice I C S n = (Option (I n × Selection (C n)) × Tape S n) := rfl

/-- The canonical row list enumerates every Boolean assignment by `Finset.univ.toList`. -/
noncomputable def rows {m : ℕ} (C : DAGCircuit m) (i : Fin C.gates.length) :
    List (Fin C.gates[i.val].args.length → Bool) := Finset.univ.toList

/-- `rows C i = Finset.univ.toList` for the gate's assignment type. -/
theorem rows_eq {m : ℕ} (C : DAGCircuit m) (i : Fin C.gates.length) :
    rows C i = (Finset.univ : Finset (Fin C.gates[i.val].args.length → Bool)).toList := rfl

/-- Every Boolean assignment occurs in the canonical row list. -/
theorem rows_complete {m : ℕ} (C : DAGCircuit m) (i : Fin C.gates.length)
    (a : Fin C.gates[i.val].args.length → Bool) : a ∈ rows C i :=
  Eq.mpr (congrArg (fun xs : List (Fin C.gates[i.val].args.length → Bool) => a ∈ xs)
    (rows_eq C i)) (Finset.mem_toList.mpr (Finset.mem_univ a))

/-- The canonical row list has no repeated assignments. -/
theorem rows_nodup {m : ℕ} (C : DAGCircuit m) (i : Fin C.gates.length) : (rows C i).Nodup :=
  Eq.mpr (congrArg List.Nodup (rows_eq C i)) (Finset.nodup_toList _)

/-- A size-S fan-in-two circuit's full selected occurrence list fits in `4*S(n)+1` slots,
for every row permutation and selected vertex. [PS10, Theorem 163.7] -/
theorem capacity {m : ℕ} (C : DAGCircuit m) (S : PolyExpr) (n : ℕ)
    (perm : (i : Fin C.gates.length) → Equiv.Perm (Fin C.gates[i.val].args.length → Bool))
    (u : ℕ) (hSize : C.size ≤ S.eval n) (hfanin : C.IsFaninTwo) :
    (GateOccurrences.occurrences C (rows C) perm u).length ≤
      (SelectedAdviceBounds.slotBudget S).eval n + 1 := by
  have hc := GateOccurrences.length_occurrences_le C (rows C) perm u (rows_nodup C) hfanin
  have hg : C.gates.length ≤ S.eval n := by
    rw [DAGCircuit.size_eq] at hSize
    omega
  rw [SelectedAdviceBounds.slotBudget_eval]
  omega

section Data

variable {I : ℕ → Type} {inputs : ℕ → ℕ} (C : ∀ n, DAGCircuit (inputs n))
  (S A B O : PolyExpr)
  (seed : ∀ n, List Bool →
    GarbleSeed (C n) (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
  (v : ∀ n, I n → ℕ → Bool) (output : ∀ n, Fin (O.eval n) → ℕ)
  (bobWord aliceWord : ∀ n, I n → List Bool) (E₁ E₂ : List Bool → List Bool)

/-- A real choice uses its selected row offsets; the absent choice uses offset zero. -/
noncomputable def offset (n : ℕ) (a : Choice I C S n) :
    Fin ((SelectedAdviceBounds.slotBudget S).eval n + 1) → ℕ :=
  match a with
  | (none, _) => fun _ => 0
  | (some (_, b), t) => SelectedPlan.slotOffset (C n) (rows (C n))
      (seed n (List.ofFn t)) (wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n)

/-- The absent choice's offset vector is constantly zero. -/
theorem offset_none (n : ℕ) (t : Tape S n) :
    offset (I := I) C S seed n (none, t) = fun _ => 0 := rfl

/-- A real choice's offsets are exactly the complete selected occurrence plan. -/
theorem offset_some (n : ℕ) (z : I n) (b : Selection (C n)) (t : Tape S n) :
    offset C S seed n (some (z, b), t) = SelectedPlan.slotOffset (C n) (rows (C n))
      (seed n (List.ofFn t)) (wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n) := rfl

/-- A real choice uses the selected row message lengths; the absent choice uses zero. -/
noncomputable def len (n : ℕ) (a : Choice I C S n) :
    Fin ((SelectedAdviceBounds.slotBudget S).eval n + 1) → ℕ :=
  match a with
  | (none, _) => fun _ => 0
  | (some (_, b), t) => SelectedPlan.slotLength (C n) (rows (C n))
      (seed n (List.ofFn t)) (wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n)

/-- The absent choice's message-length vector is constantly zero. -/
theorem len_none (n : ℕ) (t : Tape S n) :
    len (I := I) C S seed n (none, t) = fun _ => 0 := rfl

/-- A real choice's lengths are exactly the complete selected occurrence plan. -/
theorem len_some (n : ℕ) (z : I n) (b : Selection (C n)) (t : Tape S n) :
    len C S seed n (some (z, b), t) = SelectedPlan.slotLength (C n) (rows (C n))
      (seed n (List.ofFn t)) (wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n) := rfl

/-- The chosen side supplies its fixed plaintext keys to every selected occurrence; an
absent choice supplies the unique empty messages. -/
noncomputable def message (side : Bool) (n : ℕ) (a : Choice I C S n) :
    ∀ j, Fin (len C S seed n a j) → Bool :=
  match a with
  | (none, _) => fun _ _ => false
  | (some (z, b), t) => SelectedPlan.slotMessage (C n) (rows (C n))
      (seed n (List.ofFn t)) (wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n) E₁
      (fun i a => keyAt (C n) (seed n (List.ofFn t)) (inputs n + i.val)
        (GateHybrids.stageBit (C n) (v n z) (2 * b.1.val + b.2.val + side.toNat) i a))

/-- The absent choice uses the constant-false function on each empty message type. -/
theorem message_none (side : Bool) (n : ℕ) (t : Tape S n) :
    message C S seed v E₁ side n (none, t) = fun _ _ => false := rfl

/-- A real choice's side-specific messages are exactly the selected occurrence plan at
stage `2*gate+position+side.toNat`. -/
theorem message_some (side : Bool) (n : ℕ) (z : I n) (b : Selection (C n)) (t : Tape S n) :
    message C S seed v E₁ side n (some (z, b), t) =
      SelectedPlan.slotMessage (C n) (rows (C n)) (seed n (List.ofFn t)) (wire (C n) b)
        ((SelectedAdviceBounds.slotBudget S).eval n) E₁
        (fun i a => keyAt (C n) (seed n (List.ofFn t)) (inputs n + i.val)
          (GateHybrids.stageBit (C n) (v n z) (2 * b.1.val + b.2.val + side.toNat) i a)) := rfl

/-- Real advice is the fixed before-stage descriptor/view word. The absent choice uses
empty advice. Both sides use this same word, independent of the challenge key/nonces. -/
noncomputable def advice (n : ℕ) (a : Choice I C S n) : List Bool :=
  match a with
  | (none, _) => []
  | (some (z, b), t) => SelectedPlan.advice (C n) (rows (C n)) (seed n (List.ofFn t))
      (wire (C n) b) E₁ E₂ (fun i a => keyAt (C n) (seed n (List.ofFn t)) (inputs n + i.val)
        (GateHybrids.stageBit (C n) (v n z) (2 * b.1.val + b.2.val) i a))
      (pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) (C n) (seed n (List.ofFn t))
        (A.eval n) (O.eval n) (output n) (v n z) (2 * b.1.val + b.2.val)))
      (pairEncode (bobWord n z)
        (List.ofFn (FakeObjects.activeAnswers (C n) (seed n (List.ofFn t)) (A.eval n)
          (B.eval n)))) (aliceWord n z)

/-- The absent choice has empty advice. -/
theorem advice_none (n : ℕ) (t : Tape S n) :
    advice C S A B O seed v output bobWord aliceWord E₁ E₂ n (none, t) = [] := rfl

/-- Real advice is the complete fixed before-stage selected-plan advice word. -/
theorem advice_some (n : ℕ) (z : I n) (b : Selection (C n)) (t : Tape S n) :
    advice C S A B O seed v output bobWord aliceWord E₁ E₂ n (some (z, b), t) =
      SelectedPlan.advice (C n) (rows (C n)) (seed n (List.ofFn t)) (wire (C n) b) E₁ E₂
        (fun i a => keyAt (C n) (seed n (List.ofFn t)) (inputs n + i.val)
          (GateHybrids.stageBit (C n) (v n z) (2 * b.1.val + b.2.val) i a))
        (pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) (C n) (seed n (List.ofFn t))
          (A.eval n) (O.eval n) (output n) (v n z) (2 * b.1.val + b.2.val)))
        (pairEncode (bobWord n z)
          (List.ofFn (FakeObjects.activeAnswers (C n) (seed n (List.ofFn t)) (A.eval n)
            (B.eval n)))) (aliceWord n z) := rfl

/-- Every choice's slice fits in a joint pad of length at least `7n+2`. The absent choice
has offset and message length zero; real choices use the existing selected-plan fit.

**Proof sketch.** Split the optional selection. The empty case needs only n bits and fits
the supplied lower bound. In the real case the published selected-plan inequality bounds
the slice endpoint by 7n+2, which the joint pad length bounds in turn. -/
theorem fits (L : PolyExpr) (hL : ∀ n, 7 * n + 2 ≤ L.eval n)
    (n : ℕ) (a : Choice I C S n) (j : Fin ((SelectedAdviceBounds.slotBudget S).eval n + 1)) :
    offset C S seed n a j + n + len C S seed n a j ≤ L.eval n := by
  rcases a with ⟨a, t⟩
  cases a with
  | none =>
    rw [offset_none, len_none]
    change 0 + n + 0 ≤ L.eval n
    have hl := hL n
    omega
  | some a =>
    rcases a with ⟨z, b⟩
    rw [offset_some, len_some]
    have hf := SelectedPlan.slots_fit (C n) (rows (C n)) (seed n (List.ofFn t))
      (wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n) j
    have hl := hL n
    omega

/-- Every finite advice choice has length at most `sampleBudget S A B O R`, whenever
circuit size and the retained input/output words have their stated bounds.
[PS10, Theorem 163.7]

**Proof sketch.** Empty advice satisfies every natural-number budget. For a real selection,
apply the existing complete sample-advice budget to its baseline seed, selected vertex and
before-stage plaintext family. The row reader supplies the required canonical enumeration. -/
theorem advice_budget (R : PolyExpr) (hSize : ∀ n, (C n).size ≤ S.eval n)
    (hfanin : ∀ n, (C n).IsFaninTwo)
    (hBob : ∀ n z, (bobWord n z).length ≤ B.eval n)
    (hAlice : ∀ n z, (aliceWord n z).length ≤ R.eval n)
    (n : ℕ) (a : Choice I C S n) :
    (advice C S A B O seed v output bobWord aliceWord E₁ E₂ n a).length ≤
      (SelectedAdviceBounds.sampleBudget S A B O R).eval n := by
  rcases a with ⟨a, t⟩
  cases a with
  | none =>
    rw [advice_none, List.length_nil]
    exact Nat.zero_le _
  | some a =>
    rcases a with ⟨z, b⟩
    rw [advice_some]
    exact SelectedAdviceBounds.sample_advice_budget E₁ E₂ (C n) (rows (C n))
      (seed n (List.ofFn t)) (wire (C n) b)
      (fun i a => keyAt (C n) (seed n (List.ofFn t)) (inputs n + i.val)
        (GateHybrids.stageBit (C n) (v n z) (2 * b.1.val + b.2.val) i a))
      S A B O R (output n) (v n z) (2 * b.1.val + b.2.val) (bobWord n z) (aliceWord n z)
      (hfanin n) (hSize n) (rows_eq (C n)) (hBob n z) (hAlice n z)

section Joint

variable {L : PolyExpr} {L₂ : ℕ → ℕ}
  (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L.eval n) → Bool))
  (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool))
  (hG : ∀ n (s x : Fin n → Bool),
    List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hG hGE₁ hGE₂ in
/-- At every real choice, reconstructing either side's slice experiment with the common
choice advice gives exactly the corresponding actual hybrid sample under the filled seed.
All structural premises are discharged from circuit size, fan-in, consistency and sinks.
[PS10, Theorem 163.7]

**Proof sketch.** Apply the proved selected-step contract to the actual selected position.
The finite wire reader identifies its vertex; the canonical row reader fixes the row order,
and the existing occurrence bound supplies all padded slots. The two side-specific messages
and common before-stage advice are exactly the public choice maps. -/
theorem rebuild_some (hSize : ∀ n, (C n).size ≤ S.eval n)
    (hfanin : ∀ n, (C n).IsFaninTwo)
    (hEval : ∀ n z (i : Fin (C n).gates.length),
      gateOut ((C n).gates[i]) (RelabelGarbling.argValues (C n) (v n z) i) =
        v n z (inputs n + i))
    (hsink : ∀ n j g, g ∈ (C n).gates → output n j ∉ g.args)
    (n : ℕ) (z : I n) (b : Selection (C n)) (t : Tape S n)
    (k : Fin n → Bool)
    (rs : Fin ((SelectedAdviceBounds.slotBudget S).eval n + 1) → Fin n → Bool)
    (side : Bool) :
    SliceReconstruction.rebuild E₂ (pairEncode (List.replicate n true) (pairEncode
      (sliceMultiEncDist G n ((SelectedAdviceBounds.slotBudget S).eval n)
        (offset C S seed n (some (z, b), t)) (len C S seed n (some (z, b), t))
        (message C S seed v E₁ side n (some (z, b), t)) (k, rs))
      (advice C S A B O seed v output bobWord aliceWord E₁ E₂ n (some (z, b), t)))) =
      GateHybridMessage.sample (nestedSpecial E₁ E₂ n) (C n)
        (SelectedSeed.fill (C n) (rows (C n)) (seed n (List.ofFn t)) (wire (C n) b)
          ((SelectedAdviceBounds.slotBudget S).eval n) k rs)
        (A.eval n) (B.eval n) (O.eval n) (output n) (v n z) (List.replicate n true)
        (bobWord n z) [] (aliceWord n z) (2 * b.1.val + b.2.val + side.toNat) :=
  SelectedStep.reconstruct G G₁ G₂ E₁ E₂ hG hGE₁ hGE₂ (C n) (rows (C n))
    (seed n (List.ofFn t)) (wire (C n) b) ((SelectedAdviceBounds.slotBudget S).eval n)
    (v n z) (hfanin n) (hEval n z) b.1 b.2 (wire_val (C n) b).symm
    (capacity (C n) S n (seed n (List.ofFn t)).2.2 (wire (C n) b).val (hSize n) (hfanin n))
    (rows_eq (C n)) (A.eval n) (B.eval n) (O.eval n) (output n) (hsink n)
    (List.replicate n true) (bobWord n z) (aliceWord n z) k rs side

end Joint

end Data

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedStepChoices
