/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeObjects
import TCSlib.Cryptography.Asymptotic.OneWay

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time simulated garbling programs

The simulated garbler shares the real garbler's addressed key, nonce, row, and bounded table
machines. Its output-key bit is always false; output decoding pairs use the prescribed
result bits. All circuit families and seed equations remain parameters.

## Main definitions

None.

## Main results

* `FakeProgram.activeAnswers_word`: the canonical flat answer is the concatenated key blocks.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (simulation for Bob).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- The canonical simulated answer is the concatenation of the false-key blocks beginning
at vertex `first`: `ofFn (activeAnswers C s first count) = flatten (ofFn (ofFn ∘ key0))`.
This reuses the published generic tuple-block identity. [PS10, Theorem 163.7] -/
theorem activeAnswers_word {inputs width : ℕ} {ρ : Type} (C : DAGCircuit inputs)
    (s : GarbleSeed C (Fin width → Bool) ρ) (first count : ℕ) :
    List.ofFn (FakeObjects.activeAnswers C s first count) =
      (List.ofFn fun i : Fin count => List.ofFn (keyAt C s (first + i) false)).flatten := by
  have heq : FakeObjects.activeAnswers C s first count =
      (FunFamily.blocks count width).symm (fun i => keyAt C s (first + i) false) := by
    funext t
    rw [FakeObjects.activeAnswers_eq, FunFamily.blocks_symm_apply]
  rw [heq, FunFamily.ofFn_blocks_symm]

/-- The canonical flat false-key answer is polynomial-time from unary width, bound,
starting vertex and count maps, a polynomial-time coin word, a valid input range, and the
seed's addressed-key equation. [PS10, Theorem 163.7]

**Proof sketch.** On an indexed retained input, add the unary index to the starting vertex
and read its false-key window. The public data-dependent concatenation loop emits one such
block per requested vertex. The generic tuple-block identity identifies this concatenation
with the canonical finite answer; the valid-range bound justifies every seed key reader. -/
theorem activeAnswers_poly (width bound first count inputs : List Bool → ℕ)
    (coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hfirst : PolyTimeComputable fun z => List.replicate (first z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hrange : ∀ z, first z + count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z =>
      List.ofFn (FakeObjects.activeAnswers (C z) (s z) (first z) (count z)) := by
  let entry := fun z i => RowFromCoins.keyWord width bound (fun v => first v + i)
    (fun _ => false) coins z
  have hv := unaryAdd_poly (hfirst.comp polyTimeComputable_pairSndD)
    (unaryLength_poly polyTimeComputable_pairFstD)
  have he : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length := by
    refine (RowFromCoins.keyWord_poly (hcoins.comp polyTimeComputable_pairSndD)
      (hwidth.comp polyTimeComputable_pairSndD) (hbound.comp polyTimeComputable_pairSndD)
      hv (polyTimeComputable_const [false])).congr fun w => ?_
    simp only [entry, RowFromCoins.keyWord_eq]
  refine (ColMachines.polyTimeComputable_flatMap_range he hcount).congr fun z => ?_
  rw [activeAnswers_word, List.flatMap_def]
  apply congrArg List.flatten
  symm
  apply ofFn_eq_map_range
  intro i
  dsimp only [entry]
  rw [RowFromCoins.keyWord_eq]
  apply congrArg List.ofFn
  apply hkey
  rw [DAGCircuit.size_eq]
  have := hrange z
  omega

/-- Swapping each encoded pair according to the corresponding bit of a polynomial-time
result word preserves polynomial time. The pair vector is supplied by a polynomial-time
canonical encoding, and its unary length is polynomial-time. [PS10, Theorem 163.7]

**Proof sketch.** At a unary index, read the pair from its canonical word vector and read
the corresponding result bit. A conditional either swaps the two public pair projections
or retains the original pair. The existing indexed word-vector assembler encodes all these
entries; canonical list lookup identifies each entry with the requested pair. -/
theorem swapPairs_poly (count : List Bool → ℕ) (pairs result : List Bool → List Bool)
    (value : ∀ z, Fin (count z) → List Bool × List Bool)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hpairs : PolyTimeComputable pairs) (hresult : PolyTimeComputable result)
    (hshape : ∀ z, pairs z = BinArith.encWords (List.ofFn fun j =>
      pairEncode (value z j).1 (value z j).2)) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j =>
      if (result z).getD j false then pairEncode (value z j).2 (value z j).1
      else pairEncode (value z j).1 (value z j).2) := by
  let lookup := fun z i => BinArith.getW (pairEncode (List.replicate i true) (pairs z))
  let entry := fun z i => if (result z).getD i false then
    pairEncode (pairSndD (lookup z i)) (pairFstD (lookup z i)) else lookup z i
  have hl : PolyTimeComputable fun w => lookup (pairSndD w) (pairFstD w).length :=
    BinArith.polyTimeComputable_getW.comp
      ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
        (hpairs.comp polyTimeComputable_pairSndD))
  have hb : PolyTimeComputable fun w =>
      [(result (pairSndD w)).getD (pairFstD w).length false] :=
    getBit_poly (hresult.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)
  have he : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length :=
    polyTimeComputable_ite hb
      ((polyTimeComputable_pairSndD.comp hl).pairEncode
        (polyTimeComputable_pairFstD.comp hl)) hl
  refine WordLists.ofFnTable_poly _ entry hcount he ?_
  intro z j
  have hlookup : lookup z j = pairEncode (value z j).1 (value z j).2 := by
    dsimp only [lookup]
    rw [hshape z, BinArith.getW_pairEncode, List.length_replicate]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]
  dsimp only [entry]
  rw [hlookup, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The encoded simulated decoding-pair vector is polynomial-time from the real output
pair readers and a polynomial-time prescribed result word. Each result bit swaps the
corresponding two keys. [PS10, Theorem 163.7] -/
theorem outputPairs_poly (width bound count inputs : List Bool → ℕ)
    (description coins result : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (hresult : PolyTimeComputable result) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (count z) → ℕ)
    (houtsWord : ∀ z, pairSndD (description z) =
      BinArith.encWords (List.ofFn fun j => encodeNat (output z j)))
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j : Fin (count z) =>
      pairEncode (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
        ((result z).getD j false)).1)
        (List.ofFn (FakeObjects.decodePair (C z) (s z) (output z j)
          ((result z).getD j false)).2)) := by
  let value := fun z (j : Fin (count z)) =>
    (List.ofFn (keyAt (C z) (s z) (output z j) false),
      List.ofFn (keyAt (C z) (s z) (output z j) true))
  let pairs := fun z => BinArith.encWords (List.ofFn fun j =>
    pairEncode (value z j).1 (value z j).2)
  have hp : PolyTimeComputable pairs := AliceProgram.outputPairs_poly
    width bound count inputs description coins hwidth hbound hcount hdescription hcoins
    C s output houtsWord houtput_lt hkey
  refine (swapPairs_poly count pairs result value hcount hp hresult (fun _ => rfl)).congr
    fun z => ?_
  apply congrArg BinArith.encWords
  apply congrArg List.ofFn
  funext j
  cases hb : (result z).getD j false <;>
    simp [value, hb, FakeObjects.decodePair_eq]

/-- The encoded simulated Alice input-key vector contains the false key at every input
vertex and is polynomial-time under the real selected-key reader hypotheses.
[PS10, Theorem 163.7] -/
theorem inputKeys_poly (width bound count inputs : List Bool → ℕ)
    (coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hcount_le : ∀ z, count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun v : Fin (count z) =>
      List.ofFn (keyAt (C z) (s z) v false)) := by
  simpa only [List.getD_nil] using AliceProgram.selectedKeys_poly width bound count inputs
    (fun _ => []) coins hwidth hbound hcount (polyTimeComputable_const []) hcoins
    C s hcount_le hkey

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeProgram
