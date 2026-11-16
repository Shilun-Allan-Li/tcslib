/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinSeedRelabel
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeObjects

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

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids
