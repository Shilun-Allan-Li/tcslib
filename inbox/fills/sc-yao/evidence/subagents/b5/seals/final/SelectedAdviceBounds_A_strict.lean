/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedPlan
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Lengths
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
# Polynomial advice bounds for selected-key reconstruction

Each unaffected row is one fixed nested ciphertext. Each selected row stores a unary
challenge index and at most one known key/nonce pair. At most four rows per gate therefore
give a polynomial descriptor word, with explicit constants independent of all key values.
The fixed surrounding fields are accounted for separately by their word lengths.

## Main definitions

* `budget`: a polynomial budget for the full reconstruction advice.
* `slotBudget`, `tailBudget`, `privateBudget`, `sampleBudget`: concrete hybrid-view budgets.

## Main results

* `SelectedAdviceBounds.record_le`: at most `2q+7n+8` bits per row record.
* Complete descriptor-table and surrounding-advice bounds.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (polynomial-length nonuniform reconstruction advice).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds

open Complexity Turing BoolCircuit TCSlib.Cryptography

/-- Every reconstruction record has at most `2q+7n+8` bits when the padded occurrence list
fits in `q+1` slots. This includes fixed zero/unselected rows and all selected layers.

**Proof sketch.** A fixed record adds two bits to a nested ciphertext, whose length is at
most `7n+4`. A selected record has index at most `q`, so its direct or wrapped descriptor
has at most `2q+3n+8` bits. Both bounds are at most the stated common bound. -/
theorem record_le {m n : ℕ} (E₁ E₂ : List Bool → List Bool) (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) :
    (SelectedPlan.record C rows s u E₁ E₂ o i a).length ≤ 2 * q + 7 * n + 8 := by
  rw [SelectedPlan.record_eq]
  cases hsel : GateOccurrences.selectedPosition C.gates[i.val] a u.val with
  | none =>
    simp only [Option.elim_none]
    have hc := length_nestedSpecial_enc_le E₁ E₂ n (argKeys C s i a) (o i a) (s.2.1 i a)
    rw [(SliceReconstruction.record_lengths _ 0 [] []).1]
    omega
  | some p =>
    simp only [Option.elim_some]
    obtain ⟨hvertex, hbit⟩ :=
      (GateOccurrences.selectedPosition_eq_some_iff _ _ _ (hargs i) p).mp hsel
    have hi := lt_of_lt_of_le
      (SelectedSeed.slotIndex_lt C rows s.2.2 u.val i a p (hargs i)
        (hcomplete i) hvertex hbit) hcap
    have hd := SelectedRows.descriptor_length_le n q (argKeys C s i a) (s.2.1 i a)
      p.val (SelectedSeed.slotIndex C rows s.2.2 u.val i a p) (by omega)
    exact hd.trans (by omega)

/-- An encoded descriptor table has at most `4(2(2q+7n+8)+2)` bits when its row enumeration
has length at most four and the occurrence list fits the padded capacity.

**Proof sketch.** Every row record satisfies the common record bound. The public encoded-list
length bound charges twice that record length plus two delimiter bits per row. At most four
rows give the stated total. -/
theorem table_le {m n : ℕ} (E₁ E₂ : List Bool → List Bool) (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (hrowlen : ∀ i, (rows i).length ≤ 4) (i : Fin C.gates.length) :
    (BinArith.encWords ((rows i).map fun a =>
      SelectedPlan.record C rows s u E₁ E₂ o i (s.2.2 i a))).length ≤
        4 * (2 * (2 * q + 7 * n + 8) + 2) := by
  have ht := BinArith.length_encWords_le ((rows i).map fun a =>
    SelectedPlan.record C rows s u E₁ E₂ o i (s.2.2 i a)) (2 * q + 7 * n + 8) (by
      intro w hw
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hw
      exact record_le E₁ E₂ C rows s u q o hargs hcomplete hcap i (s.2.2 i a))
  simp only [List.length_map] at ht
  exact ht.trans (Nat.mul_le_mul_right _ (hrowlen i))

/-- The encoded descriptor-table word has at most
`C.gates.length * (16*(2q+7n+8)+18)` bits, with at most four rows at each gate.

**Proof sketch.** Each encoded table has the bound from `table_le`. Apply the encoded-list
length bound once more to the gate-index vector. Its length is the gate count; simplifying
the two layers of delimiter costs gives the displayed coefficient. -/
theorem encodedTables_le {m n : ℕ} (E₁ E₂ : List Bool → List Bool) (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (hrowlen : ∀ i, (rows i).length ≤ 4) :
    (BinArith.encWords ((SelectedPlan.tables C rows s u E₁ E₂ o).map BinArith.encWords)).length ≤
      C.gates.length * (16 * (2 * q + 7 * n + 8) + 18) := by
  rw [SelectedPlan.tables_eq, List.map_ofFn]
  have ht := BinArith.length_encWords_le
    (List.ofFn fun i => BinArith.encWords ((rows i).map fun a =>
      SelectedPlan.record C rows s u E₁ E₂ o i (s.2.2 i a)))
    (4 * (2 * (2 * q + 7 * n + 8) + 2)) (by
      intro w hw
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
      exact table_le E₁ E₂ C rows s u q o hargs hcomplete hcap hrowlen i)
  have hc : 2 * (4 * (2 * (2 * q + 7 * n + 8) + 2)) + 2 =
      16 * (2 * q + 7 * n + 8) + 18 := by omega
  simpa only [List.length_ofFn, hc] using ht

/-- Full reconstruction advice has at most
`2G*(16*(2q+7n+8)+18)+2|tail|+2|privateInput|+|aliceOutput|+6` bits, where `G` is the gate count. -/
theorem advice_le {m n : ℕ} (E₁ E₂ : List Bool → List Bool) (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (hrowlen : ∀ i, (rows i).length ≤ 4) (tail privateInput aliceOutput : List Bool) :
    (SliceReconstruction.advice
      (BinArith.encWords ((SelectedPlan.tables C rows s u E₁ E₂ o).map BinArith.encWords))
      tail privateInput aliceOutput).length ≤
        2 * C.gates.length * (16 * (2 * q + 7 * n + 8) + 18) +
          2 * tail.length + 2 * privateInput.length + aliceOutput.length + 6 := by
  rw [SliceReconstruction.advice_length]
  have ht := Nat.mul_le_mul_left 2
    (encodedTables_le E₁ E₂ C rows s u q o hargs hcomplete hcap hrowlen)
  simp only [Nat.mul_assoc] at ht ⊢
  omega

/-- The polynomial advice budget for gate bound `S`, slot bound `Q`, and surrounding-field
bounds `T,I,A` is `2S(16(2Q+7n+8)+18)+2T+2I+A+6`. -/
def budget (S Q T I A : PolyExpr) : PolyExpr :=
  let row : PolyExpr := .add (.add (.mul (.const 2) Q) (.mul (.const 7) .var)) (.const 8)
  let descriptors : PolyExpr := .mul (.mul (.const 2) S)
    (.add (.mul (.const 16) row) (.const 18))
  .add (.add (.add (.add descriptors (.mul (.const 2) T)) (.mul (.const 2) I)) A) (.const 6)

/-- `budget` is the displayed composition of polynomial addition, multiplication and constants. -/
theorem budget_eq (S Q T I A : PolyExpr) :
    budget S Q T I A =
      let row : PolyExpr := .add (.add (.mul (.const 2) Q) (.mul (.const 7) .var)) (.const 8)
      let descriptors : PolyExpr := .mul (.mul (.const 2) S)
        (.add (.mul (.const 16) row) (.const 18))
      .add (.add (.add (.add descriptors (.mul (.const 2) T)) (.mul (.const 2) I)) A) (.const 6) :=
  rfl

/-- Evaluating the advice budget gives the explicit natural-number bound
`2S(n)(16(2Q(n)+7n+8)+18)+2T(n)+2I(n)+A(n)+6`. -/
theorem budget_eval (S Q T I A : PolyExpr) (n : ℕ) :
    (budget S Q T I A).eval n =
      2 * S.eval n * (16 * (2 * Q.eval n + 7 * n + 8) + 18) +
        2 * T.eval n + 2 * I.eval n + A.eval n + 6 := by
  simp only [budget_eq, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The full advice length is bounded by the explicit polynomial `budget S Q T I A` whenever
the gate count, slot parameter and three fixed surrounding fields have these polynomial
bounds. This makes the polynomial-advice claim explicit for this encoding.
[PS10, Theorem 163.7]

**Proof sketch.** Start with the pointwise advice bound. Enlarge the row-record coefficient
using the slot polynomial, and enlarge the descriptor-table count using the gate polynomial.
Monotonicity gives the resulting product bound. Add the bounds for the fixed surrounding
fields, and evaluate the published budget polynomial to identify the result. -/
theorem advice_budget {m n : ℕ} (E₁ E₂ : List Bool → List Bool) (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (hrowlen : ∀ i, (rows i).length ≤ 4) (tail privateInput aliceOutput : List Bool)
    (S Q T I A : PolyExpr) (hS : C.gates.length ≤ S.eval n) (hQ : q ≤ Q.eval n)
    (hT : tail.length ≤ T.eval n) (hI : privateInput.length ≤ I.eval n)
    (hA : aliceOutput.length ≤ A.eval n) :
    (SliceReconstruction.advice
      (BinArith.encWords ((SelectedPlan.tables C rows s u E₁ E₂ o).map BinArith.encWords))
      tail privateInput aliceOutput).length ≤ (budget S Q T I A).eval n := by
  have hrow : 2 * q + 7 * n + 8 ≤ 2 * Q.eval n + 7 * n + 8 := by omega
  have hcoeff : 16 * (2 * q + 7 * n + 8) + 18 ≤
      16 * (2 * Q.eval n + 7 * n + 8) + 18 := by omega
  have hprod := Nat.mul_le_mul hS hcoeff
  have hscaled := Nat.mul_le_mul_left 2 hprod
  have hb := advice_le E₁ E₂ C rows s u q o hargs hcomplete hcap hrowlen
    tail privateInput aliceOutput
  rw [budget_eval]
  simp only [Nat.mul_assoc] at hb hscaled ⊢
  omega

/-- The hybrid message's fixed tail has at most
`2*(inA*(2n+2))+2+outLen*(6n+6)` bits, independently of its stage tables and all key values.
The bound reuses the public input-key and output-pair encoding bounds. -/
theorem messageTail_le {m n : ℕ} {ρ : Type}
    (M : MultiEnc (Fin n → Bool) (List Bool) ρ) (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ρ) (inA outLen : ℕ) (output : Fin outLen → ℕ)
    (v : ℕ → Bool) (stage : ℕ) :
    (pairSndD (GateHybridMessage.message M C s inA outLen output v stage)).length ≤
      2 * (inA * (2 * n + 2)) + 2 + outLen * (6 * n + 6) := by
  have hk : (BinArith.encWords (List.ofFn fun w : Fin inA =>
      List.ofFn (keyAt C s w false))).length ≤ inA * (2 * n + 2) := by
    simpa only [encodeMsgs_eq_encWords] using
      length_encoded_keys_le (fun w : Fin inA => keyAt C s w false)
  have hp := length_encoded_pairs_le (fun (j : Fin outLen) (b : Bool) =>
    if b then (FakeObjects.decodePair C s (output j) (v (output j))).2
    else (FakeObjects.decodePair C s (output j) (v (output j))).1)
  simp only [encodeMsgs_eq_encWords] at hp
  rw [GateHybridMessage.message_eq, pairSndD_pairEncode, length_pairEncode]
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hk) 2) hp

/-- The private view-input word has exactly `2|bobInput|+2+count*n` bits: the encoded Bob
input followed by the false-key OT answer vector. Zero key width and zero count are included. -/
theorem privateInput_length {m n : ℕ} {ρ : Type} (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ρ) (first count : ℕ) (bobInput : List Bool) :
    (pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s first count))).length =
      2 * bobInput.length + 2 + count * n := by
  rw [length_pairEncode, List.length_ofFn]

/-- The selected-key experiment has `4S(n)+1` padded nonce slots, using slot parameter `4S`. -/
def slotBudget (S : PolyExpr) : PolyExpr := .mul (.const 4) S

/-- `slotBudget S = 4*S` as a polynomial expression. -/
theorem slotBudget_eq (S : PolyExpr) : slotBudget S = .mul (.const 4) S := rfl

/-- The fixed message-tail budget is `2*A(n)*(2n+2)+2+O(n)*(6n+6)`. -/
def tailBudget (A O : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 2) (.mul A (.add (.mul (.const 2) .var) (.const 2)))) (.const 2))
    (.mul O (.add (.mul (.const 6) .var) (.const 6)))

/-- `tailBudget` combines the two public key/pair encoding bounds. -/
theorem tailBudget_eq (A O : PolyExpr) :
    tailBudget A O =
      .add (.add (.mul (.const 2) (.mul A (.add (.mul (.const 2) .var) (.const 2)))) (.const 2))
        (.mul O (.add (.mul (.const 6) .var) (.const 6))) := rfl

/-- The private view-input budget is `2B(n)+2+B(n)*n`. -/
def privateBudget (B : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 2) B) (.const 2)) (.mul B .var)

/-- `privateBudget B` is the polynomial for Bob's input paired with his active answers. -/
theorem privateBudget_eq (B : PolyExpr) :
    privateBudget B = .add (.add (.mul (.const 2) B) (.const 2)) (.mul B .var) := rfl

/-- The concrete hybrid-view advice budget uses gate bound `S`, input bounds `A,B`,
output-pair count `O`, and retained Alice-output bound `R`. -/
def sampleBudget (S A B O R : PolyExpr) : PolyExpr :=
  budget S (slotBudget S) (tailBudget A O) (privateBudget B) R

/-- `sampleBudget` instantiates the generic advice polynomial with the fixed hybrid fields. -/
theorem sampleBudget_eq (S A B O R : PolyExpr) :
    sampleBudget S A B O R = budget S (slotBudget S) (tailBudget A O) (privateBudget B) R := rfl

/-- Evaluating the slot polynomial gives `(slotBudget S)(n)=4*S(n)`. -/
theorem slotBudget_eval (S : PolyExpr) (n : ℕ) :
    (slotBudget S).eval n = 4 * S.eval n := by
  simp only [slotBudget_eq, PolyExpr.eval_mul, PolyExpr.eval_const]

/-- Evaluating the fixed message-tail budget gives
`2*A(n)*(2n+2)+2+O(n)*(6n+6)`. -/
theorem tailBudget_eval (A O : PolyExpr) (n : ℕ) :
    (tailBudget A O).eval n =
      2 * (A.eval n * (2 * n + 2)) + 2 + O.eval n * (6 * n + 6) := by
  simp only [tailBudget_eq, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- Evaluating the private-input polynomial gives `2B(n)+2+B(n)*n`. -/
theorem privateBudget_eval (B : PolyExpr) (n : ℕ) :
    (privateBudget B).eval n = 2 * B.eval n + 2 + B.eval n * n := by
  simp only [privateBudget_eq, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The complete actual hybrid-view advice has the explicit polynomial bound
`sampleBudget S A B O R`, using `4S(n)+1` padded challenge slots. The circuit, all keys,
nonces, masks, stage and prescribed outputs may be arbitrary. [PS10, Theorem 163.7]

**Proof sketch.** Fan-in two supplies distinct arguments and the canonical assignment lists
have at most four rows by the existing garbled-table bound. The all-gate occurrence bound is
at most four times the gate count, so the chosen slot polynomial covers it. The published
message-tail and private-input bounds charge all retained view fields. Substitute these
bounds into the generic advice polynomial. No key-value inequalities or positive-size
assumptions are used. -/
theorem sample_advice_budget {m n : ℕ} (E₁ E₂ : List Bool → List Bool)
    (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (S A B O R : PolyExpr) (output : Fin (O.eval n) → ℕ) (v : ℕ → Bool) (stage : ℕ)
    (bobInput aliceOutput : List Bool) (hfanin : C.IsFaninTwo)
    (hS : C.size ≤ S.eval n)
    (hrows : ∀ i, rows i = (Finset.univ : Finset (Fin C.gates[i.val].args.length → Bool)).toList)
    (hBob : bobInput.length ≤ B.eval n) (hAlice : aliceOutput.length ≤ R.eval n) :
    (SelectedPlan.advice C rows s u E₁ E₂ o
      (pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) C s
        (A.eval n) (O.eval n) output v stage))
      (pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s (A.eval n) (B.eval n))))
      aliceOutput).length ≤ (sampleBudget S A B O R).eval n := by
  have hfan := (DAGCircuit.isFaninTwo_iff C).mp hfanin
  have hargs (i : Fin C.gates.length) : C.gates[i.val].args.Nodup :=
    (hfan.1 _ (List.getElem_mem i.isLt)).1
  have hcomplete (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool) :
      a ∈ rows i := by
    rw [hrows i]
    exact Finset.mem_toList.mpr (Finset.mem_univ a)
  have hnodup (i : Fin C.gates.length) : (rows i).Nodup := by
    rw [hrows i]
    exact Finset.nodup_toList _
  have hrowlen (i : Fin C.gates.length) : (rows i).length ≤ 4 := by
    rw [hrows i]
    simpa only [garbledTable_eq, List.length_map, Fin.getElem_fin] using
      length_garbledTable_le (nestedSpecial E₁ E₂ n) C s i
        (hfan.2 _ (List.getElem_mem i.isLt))
  have hg : C.gates.length ≤ S.eval n := by
    rw [DAGCircuit.size_eq] at hS
    omega
  have hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤
      (slotBudget S).eval n + 1 := by
    have hc := GateOccurrences.length_occurrences_le C rows s.2.2 u.val hnodup hfanin
    rw [slotBudget_eval]
    omega
  have ht := messageTail_le (nestedSpecial E₁ E₂ n) C s (A.eval n) (O.eval n)
    output v stage
  have hi : (pairEncode bobInput
      (List.ofFn (FakeObjects.activeAnswers C s (A.eval n) (B.eval n)))).length ≤
        (privateBudget B).eval n := by
    rw [privateInput_length, privateBudget_eval]
    omega
  rw [SelectedPlan.advice_eq, sampleBudget_eq]
  exact advice_budget E₁ E₂ C rows s u ((slotBudget S).eval n) o hargs hcomplete hcap
    hrowlen _ _ aliceOutput S (slotBudget S) (tailBudget A O) (privateBudget B) R hg
    (Nat.le_refl _) (by simpa only [tailBudget_eval] using ht) hi hAlice

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedAdviceBounds
