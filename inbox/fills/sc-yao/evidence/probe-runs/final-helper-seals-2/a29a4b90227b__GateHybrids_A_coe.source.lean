/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinSeedRelabel
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeObjects
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
# Two-stage garbled-gate hybrids

Rows are parameterized by their output-key labels. The hybrid first replaces
rows whose first argument bit is true, then advances to the next gate. For
arity at most two, the only remaining nonzero assignment in the second step
has first bit false and second bit true. The all-zero row already has the
false label by circuit evaluation. No positive gate count is assumed.

## Main definitions

* `rowWith`, `tableWith`: garbled rows and tables with supplied output-key labels.
* `trueBit`, `outputBit`: the relabeled truth bit and the two-stage hybrid labels.
* `stageBit`: the natural-indexed family with cutoff `t / 2` and phase `t % 2`.

## Main results

* `trueBit_zero`: the active all-zero assignment encrypts the false output key.
* The generic rows and tables specialize to the public real and fake objects.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Protocol 162.6 and Theorem 163.7 (the gate-by-gate hybrid).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids

open BoolCircuit TCSlib.Cryptography

variable {K Cipher ρ : Type} [Inhabited K] {inputs : ℕ}

/-- A row with output-key label `bit i a` encrypts that key under the ordinary
argument keys, using the row's existing seed coins. [PS10, Theorem 163.7] -/
def rowWith (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs) (s : GarbleSeed C K ρ)
    (bit : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) : Cipher :=
  M.enc (argKeys C s i a) (keyAt C s (inputs + i) (bit i a)) (s.2.1 i a)

/-- `rowWith ... bit i a` is the encryption of output key `bit i a` with the
ordinary argument keys and row coins. -/
theorem rowWith_eq (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ)
    (bit : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    rowWith M C s bit i a =
      M.enc (argKeys C s i a) (keyAt C s (inputs + i) (bit i a)) (s.2.1 i a) := rfl

/-- A table with labels `bit` uses the public fixed assignment enumeration and
its seed's row permutation. [PS10, Theorem 163.7] -/
noncomputable def tableWith (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ)
    (bit : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) : List Cipher :=
  (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map
    fun a => rowWith M C s bit i (s.2.2 i a)

/-- `tableWith ... bit i` enumerates `rowWith ... bit i (s.perm i a)` in the
public fixed assignment order. -/
theorem tableWith_eq (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ)
    (bit : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) :
    tableWith M C s bit i =
      (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map
        fun a => rowWith M C s bit i (s.2.2 i a) := rfl

/-- Equal output labels at every assignment of a gate give equal generic tables. -/
theorem tableWith_congr (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ)
    (bit bit' : ∀ i : Fin C.gates.length, (Fin (C.gates[i]).args.length → Bool) → Bool)
    (i : Fin C.gates.length) (h : ∀ a, bit i a = bit' i a) :
    tableWith M C s bit i = tableWith M C s bit' i := by
  rw [tableWith_eq, tableWith_eq]
  apply List.map_congr_left
  intro a _
  rw [rowWith_eq, rowWith_eq, h]

/-- With the gate's ordinary truth function as labels, `rowWith` equals the
published real garbled row. This is a specialization, with no new row semantics. -/
theorem rowWith_real (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    rowWith M C s (fun j b => gateOut (C.gates[j]) b) i a = garbledRow M C s i a := by
  rw [rowWith_eq, garbledRow_eq]

/-- With all-false labels, `rowWith` equals `FakeObjects.row` exactly. -/
theorem rowWith_fake (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    rowWith M C s (fun _ _ => false) i a = FakeObjects.row M C s i a := by
  rw [rowWith_eq, FakeObjects.row_eq]

/-- The generic table with ordinary truth labels is exactly `garbledTable`. -/
theorem tableWith_real (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    tableWith M C s (fun j b => gateOut (C.gates[j]) b) i = garbledTable M C s i := by
  simp only [tableWith_eq, garbledTable_eq, rowWith_real]

/-- The generic table with all-false labels is exactly `FakeObjects.table`. -/
theorem tableWith_fake (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    tableWith M C s (fun _ _ => false) i = FakeObjects.table M C s i := by
  simp only [tableWith_eq, FakeObjects.table_eq, rowWith_fake]

/-- The relabeled truth bit is the original truth bit after argument-value XOR,
then XORed with the actual output-wire value. [PS10, Theorem 163.7] -/
def trueBit (C : DAGCircuit inputs) (v : ℕ → Bool) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) : Bool :=
  xor (gateOut (C.gates[i]) (xorPerm (RelabelGarbling.argValues C v i) a)) (v (inputs + i))

/-- `trueBit C v i a = gateOut(g_i)(a XOR v_args) XOR v(inputs+i)`. -/
theorem trueBit_eq (C : DAGCircuit inputs) (v : ℕ → Bool) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) :
    trueBit C v i a =
      xor (gateOut (C.gates[i]) (xorPerm (RelabelGarbling.argValues C v i) a))
        (v (inputs + i)) := rfl

/-- At a circuit-consistent wire-value map, the all-zero assignment has the
false relabeled output bit. This includes constant gates. [PS10, Theorem 163.7] -/
theorem trueBit_zero (C : DAGCircuit inputs) (v : ℕ → Bool)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (inputs + i))
    (i : Fin C.gates.length) : trueBit C v i (fun _ => false) = false := by
  have hz : xorPerm (RelabelGarbling.argValues C v i) (fun _ => false) =
      RelabelGarbling.argValues C v i := by
    funext t
    simp only [xorPerm_apply, Bool.false_xor]
  rw [trueBit_eq, hz, hEval i, Bool.xor_self]

/-- Circuit evaluation provides the gate-consistency equation needed by the
all-zero-row lemma, using the published circuit-value and gate-output readers. -/
theorem values_consistent (C : DAGCircuit inputs) (x : Fin inputs → Bool)
    (i : Fin C.gates.length) :
    gateOut (C.gates[i])
        (RelabelGarbling.argValues C (fun w => (C.values x).getD w false) i) =
      (C.values x).getD (inputs + i) false := by
  rw [RelabelGarbling.argValues_eq, gateOut_eq]
  simpa only [Fin.getElem_fin] using (C.values_getD_gate x i.isLt).symm

/-- The original table equals the table with relabeled truth bits under the
relabeled seed, in the same public enumeration order. [PS10, Theorem 163.7] -/
theorem tableWith_relabel (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (v : ℕ → Bool) (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    garbledTable M C s i =
      tableWith M C (RelabelGarbling.relabelSeed C v s) (trueBit C v) i := by
  simpa only [tableWith_eq, rowWith_eq, trueBit_eq] using
    RelabelGarbling.garbledTable_relabel C v M s i

/-- Completed gates encrypt false keys. At the current gate, nonzero phase also
replaces first-bit-true rows; all other rows retain the relabeled truth bit.
Natural cutoff and phase make the definition total for empty circuits. -/
def outputBit (C : DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) : Bool :=
  if (i : ℕ) < cutoff ∨ ((i : ℕ) = cutoff ∧ phase ≠ 0 ∧
      (List.ofFn a).getD 0 false = true) then false else trueBit C v i a

/-- `outputBit` is false at completed gates and selected current-gate rows,
and is `trueBit C v i a` at the remaining rows. -/
theorem outputBit_eq (C : DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    outputBit C v cutoff phase i a =
      if (i : ℕ) < cutoff ∨ ((i : ℕ) = cutoff ∧ phase ≠ 0 ∧
        (List.ofFn a).getD 0 false = true) then false else trueBit C v i a := rfl

/-- Stage `t` uses cutoff `t / 2` and phase `t % 2`. Thus stages `2i` and
`2i+1` are the two substeps at gate `i`. [PS10, Theorem 163.7] -/
def stageBit (C : DAGCircuit inputs) (v : ℕ → Bool) (t : ℕ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) : Bool :=
  outputBit C v (t / 2) (t % 2) i a

/-- `stageBit C v t = outputBit C v (t/2) (t%2)`. -/
theorem stageBit_eq (C : DAGCircuit inputs) (v : ℕ → Bool) (t : ℕ) :
    stageBit C v t = outputBit C v (t / 2) (t % 2) := rfl

/-- Before any gate is processed, the hybrid labels are the relabeled truth bits. -/
theorem outputBit_start (C : DAGCircuit inputs) (v : ℕ → Bool) :
    outputBit C v 0 0 = trueBit C v := by
  funext i a
  rw [outputBit_eq, if_neg (by omega)]

/-- Once the cutoff reaches the number of gates, every output label is false. -/
theorem outputBit_end (C : DAGCircuit inputs) (v : ℕ → Bool) (cutoff phase : ℕ)
    (hc : C.gates.length ≤ cutoff) :
    outputBit C v cutoff phase = fun _ _ => false := by
  funext i a
  rw [outputBit_eq, if_pos (Or.inl (lt_of_lt_of_le i.isLt hc))]

/-- Even stage `2k` is the start of gate `k`, with phase zero. -/
theorem stageBit_even (C : DAGCircuit inputs) (v : ℕ → Bool) (k : ℕ) :
    stageBit C v (2 * k) = outputBit C v k 0 := by
  rw [stageBit_eq]
  have hd : 2 * k / 2 = k := by omega
  have hm : 2 * k % 2 = 0 := by omega
  rw [hd, hm]

/-- Odd stage `2k+1` is phase one at gate `k`. -/
theorem stageBit_odd (C : DAGCircuit inputs) (v : ℕ → Bool) (k : ℕ) :
    stageBit C v (2 * k + 1) = outputBit C v k 1 := by
  rw [stageBit_eq]
  have hd : (2 * k + 1) / 2 = k := by omega
  have hm : (2 * k + 1) % 2 = 1 := by omega
  rw [hd, hm]

/-- The last natural stage has exactly the existing fake table at every gate.
The equality also covers empty circuits. [PS10, Theorem 163.7] -/
theorem tableWith_end (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (v : ℕ → Bool) (i : Fin C.gates.length) :
    tableWith M C s (stageBit C v (2 * C.gates.length)) i =
      FakeObjects.table M C s i := by
  rw [stageBit_even, outputBit_end C v C.gates.length 0 (by rfl), tableWith_fake]

/-- A completed gate's label is false at every assignment and phase. -/
theorem outputBit_completed (C : DAGCircuit inputs) (v : ℕ → Bool)
    (cutoff phase : ℕ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) (hi : (i : ℕ) < cutoff) :
    outputBit C v cutoff phase i a = false := by
  rw [outputBit_eq, if_pos (Or.inl hi)]

/-- A future gate retains its relabeled truth label at every phase. -/
theorem outputBit_future (C : DAGCircuit inputs) (v : ℕ → Bool)
    (cutoff phase : ℕ) (i : Fin C.gates.length)
    (a : Fin (C.gates[i]).args.length → Bool) (hi : cutoff < (i : ℕ)) :
    outputBit C v cutoff phase i a = trueBit C v i a := by
  rw [outputBit_eq, if_neg (by omega)]

/-- At the current gate, phase zero retains every relabeled truth label. -/
theorem outputBit_current_zero (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    outputBit C v i 0 i a = trueBit C v i a := by
  rw [outputBit_eq, if_neg (by omega)]

/-- At phase one of the current gate, every first-bit-true row encrypts false. -/
theorem outputBit_current_first (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (ha : (List.ofFn a).getD 0 false = true) :
    outputBit C v i 1 i a = false := by
  rw [outputBit_eq, if_pos (Or.inr ⟨rfl, by decide, ha⟩)]

/-- At phase one of the current gate, first-bit-false rows retain their truth label. -/
theorem outputBit_current_rest (C : DAGCircuit inputs) (v : ℕ → Bool)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (ha : (List.ofFn a).getD 0 false = false) :
    outputBit C v i 1 i a = trueBit C v i a := by
  simp only [outputBit_eq, ha, Bool.false_eq_true, and_false, or_false,
    Nat.lt_irrefl, ite_false]

/-- At a consistent wire-value map, the all-zero row stays false in every stage. -/
theorem outputBit_zero (C : DAGCircuit inputs) (v : ℕ → Bool)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (inputs + i))
    (cutoff phase : ℕ) (i : Fin C.gates.length) :
    outputBit C v cutoff phase i (fun _ => false) = false := by
  simp only [outputBit_eq, trueBit_zero C v hEval i, ite_self]

/-- For arity at most two, two false padded argument bits force the all-zero
assignment. This reuses the published binary-fold injectivity lemma. -/
theorem assignment_zero_of_two {l : ℕ} (hl : l ≤ 2) (a : Fin l → Bool)
    (h₀ : (List.ofFn a).getD 0 false = false)
    (h₁ : (List.ofFn a).getD 1 false = false) : a = fun _ => false := by
  apply CoinSeedRelabel.assignmentFold_injective l hl
  dsimp only
  rw [RowFromCoins.assignmentFold_eq_two a hl,
    RowFromCoins.assignmentFold_eq_two (fun _ : Fin l => false) hl]
  simp only [h₀, h₁, List.ofFn_const, List.getD_eq_getElem?_getD,
    List.getElem?_getD_replicate_default_eq, Bool.toNat_false]

/-- The first substep leaves every other gate and every first-bit-false row unchanged. -/
theorem outputBit_first_unchanged (C : DAGCircuit inputs) (v : ℕ → Bool)
    (cutoff : ℕ) (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (h : (i : ℕ) ≠ cutoff ∨ (List.ofFn a).getD 0 false = false) :
    outputBit C v cutoff 0 i a = outputBit C v cutoff 1 i a := by
  rcases h with hi | ha
  · simp only [outputBit_eq, hi, false_and, or_false]
  · simp only [outputBit_eq, ha, Bool.false_eq_true, and_false, or_false]

/-- Advancing the cutoff leaves every gate other than the current gate unchanged. -/
theorem outputBit_second_other (C : DAGCircuit inputs) (v : ℕ → Bool)
    (cutoff : ℕ) (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (hi : (i : ℕ) ≠ cutoff) :
    outputBit C v cutoff 1 i a = outputBit C v (cutoff + 1) 0 i a := by
  by_cases hlt : (i : ℕ) < cutoff
  · rw [outputBit_completed C v cutoff 1 i a hlt,
      outputBit_completed C v (cutoff + 1) 0 i a (by omega)]
  · rw [outputBit_future C v cutoff 1 i a (by omega)]
    rw [outputBit_eq, if_neg (by omega)]

/-- The second substep changes only current-gate rows whose first bit is false
and second bit is true, when arity is at most two and wire values are consistent.
[PS10, Theorem 163.7]

**Proof sketch.** Other gates are unchanged by the cutoff arithmetic. At the
current gate, first-bit-true rows were already replaced in phase one. If both
padded bits are false, fold injectivity identifies the all-zero assignment;
circuit consistency makes its relabeled truth bit false in every phase. These
are exactly the complementary cases to first-false/second-true selection. -/
theorem outputBit_second_unchanged (C : DAGCircuit inputs) (v : ℕ → Bool)
    (hA : ∀ i : Fin C.gates.length, (C.gates[i]).args.length ≤ 2)
    (hEval : ∀ i : Fin C.gates.length,
      gateOut (C.gates[i]) (RelabelGarbling.argValues C v i) = v (inputs + i))
    (cutoff : ℕ) (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (h : (i : ℕ) ≠ cutoff ∨ (List.ofFn a).getD 0 false = true ∨
      (List.ofFn a).getD 1 false = false) :
    outputBit C v cutoff 1 i a = outputBit C v (cutoff + 1) 0 i a := by
  by_cases hi : (i : ℕ) = cutoff
  · subst cutoff
    rcases h with hne | hfirst | hsecond
    · exact False.elim (hne rfl)
    · rw [outputBit_current_first C v i a hfirst,
        outputBit_completed C v ((i : ℕ) + 1) 0 i a (by omega)]
    · cases hfirst : (List.ofFn a).getD 0 false with
      | false =>
        have hz := assignment_zero_of_two (hA i) a hfirst hsecond
        rw [hz, outputBit_zero C v hEval, outputBit_zero C v hEval]
      | true =>
        rw [outputBit_current_first C v i a hfirst,
          outputBit_completed C v ((i : ℕ) + 1) 0 i a (by omega)]
  · exact outputBit_second_other C v cutoff i a hi

/-- Stage zero uses precisely the relabeled truth labels. -/
theorem stageBit_start (C : DAGCircuit inputs) (v : ℕ → Bool) :
    stageBit C v 0 = trueBit C v := by
  rw [stageBit_eq]
  exact outputBit_start C v

/-- The original real table equals stage zero under the relabeled seed.
This is a per-seed identity, before any uniform change of coins. -/
theorem tableWith_start (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (v : ℕ → Bool) (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    garbledTable M C s i =
      tableWith M C (RelabelGarbling.relabelSeed C v s) (stageBit C v 0) i := by
  rw [stageBit_start]
  exact tableWith_relabel M C v s i

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids
