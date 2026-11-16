/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Garbling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Active-key simulated garblings

These are new simulator objects. Every row encrypts its output vertex's false key, and
an output decoding pair is swapped according to the prescribed output bit. The ordinary
argument-key and shuffled-enumeration interfaces come from the public garbling layer.

## Main definitions

* `FakeObjects.row`, `table`: rows and shuffled tables with false active output keys.
* `FakeObjects.decodePair`: the output-key pair ordered by a prescribed bit.
* `FakeObjects.activeAnswers`: consecutive false-key blocks for selected input vertices.

## Main results

* The `_eq` readers expose every new object's formula without unfolding it.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (simulation for Bob in the OT-hybrid garbling protocol).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects

open BoolCircuit

variable {K Cipher ρ : Type} [Inhabited K] {inputs : ℕ}

/-- A simulated row encrypts the false key of vertex `inputs + i` under the assignment's
ordinary argument keys, using that row's seed coins. [PS10, Theorem 163.7]
`row M C s i a = M.enc (argKeys C s i a) (keyAt C s (inputs + i) false) (s.2.1 i a)`. -/
def row (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) : Cipher :=
  M.enc (argKeys C s i a) (keyAt C s (inputs + i) false) (s.2.1 i a)

/-- `row M C s i a = M.enc (argKeys C s i a) (keyAt C s (inputs + i) false) (s.2.1 i a)`. -/
theorem row_eq (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs) (s : GarbleSeed C K ρ)
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool) :
    row M C s i a = M.enc (argKeys C s i a) (keyAt C s (inputs + i) false) (s.2.1 i a) := rfl

/-- A simulated table enumerates all assignments in the public fixed order, applies the
seed row permutation, and emits a simulated row at every position. [PS10, Theorem 163.7]
`table M C s i = (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map fun a =>
row M C s i (s.2.2 i a)`. -/
noncomputable def table (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length) : List Cipher :=
  (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map
    fun a => row M C s i (s.2.2 i a)

/-- `table M C s i` is the fixed assignment enumeration mapped to `row M C s i (s.perm i a)`.
`table M C s i = (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map fun a =>
row M C s i (s.2.2 i a)`. -/
theorem table_eq (M : MultiEnc K Cipher ρ) (C : DAGCircuit inputs)
    (s : GarbleSeed C K ρ) (i : Fin C.gates.length) :
    table M C s i =
      (Finset.univ : Finset (Fin (C.gates[i]).args.length → Bool)).toList.map
        fun a => row M C s i (s.2.2 i a) := rfl

/-- The simulated decoding pair at vertex `v` is `(key_v(b), key_v(!b))`, placing the
false active key at the position named by the prescribed result `b`. [PS10, Theorem 163.7]
`decodePair C s v b = (keyAt C s v b, keyAt C s v (!b))`. -/
def decodePair (C : DAGCircuit inputs) (s : GarbleSeed C K ρ) (v : ℕ) (b : Bool) : K × K :=
  (keyAt C s v b, keyAt C s v (!b))

/-- `decodePair C s v b = (keyAt C s v b, keyAt C s v (!b))`. -/
theorem decodePair_eq (C : DAGCircuit inputs) (s : GarbleSeed C K ρ) (v : ℕ) (b : Bool) :
    decodePair C s v b = (keyAt C s v b, keyAt C s v (!b)) := rfl

/-- The simulated OT answer concatenates `count` false-key blocks beginning at input
vertex `first`: position `t` reads key `first + t.divNat` at coordinate `t.modNat`.
[PS10, Theorem 163.7]
`activeAnswers C s first count t = keyAt C s (first + t.divNat) false t.modNat`. -/
def activeAnswers {width : ℕ} (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) :
    Fin (count * width) → Bool :=
  fun t => keyAt C s (first + t.divNat) false t.modNat

/-- `activeAnswers C s first count t = keyAt C s (first + t.divNat) false t.modNat`. -/
theorem activeAnswers_eq {width : ℕ} (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) (t : Fin (count * width)) :
    activeAnswers C s first count t = keyAt C s (first + t.divNat) false t.modNat := rfl

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeObjects
