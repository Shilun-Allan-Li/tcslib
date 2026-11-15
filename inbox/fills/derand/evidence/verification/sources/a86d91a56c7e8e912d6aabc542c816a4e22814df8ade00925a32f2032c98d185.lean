/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Data.List.OfFn
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Circuits with paired inputs and fixed randomness

The hard-wiring step of [AB09, Thm 7.17], for the library's self-delimiting
`Turing.pairEncode`. The first component is doubled, so simply fixing a suffix
is insufficient: two buffered copies of each free input supply its two encoded
coordinates, followed by constants for the separator and the fixed second word.

## Main definitions

* `BoolCircuit.inputGate`, `inputBuffer`, `inputValues` — copy or fix circuit inputs.
* `BoolCircuit.DAGCircuit.bufferInputs` — replace a circuit's inputs by buffered sources.
* `BoolCircuit.DAGCircuit.pairEncode` — compute a circuit on `pairEncode x r` with `r` fixed.

## Main results

* `BoolCircuit.DAGCircuit.pairEncode_eval` — the paired circuit computes the original
  circuit on the encoded input and fixed random word.
* `BoolCircuit.DAGCircuit.pairEncode_isFaninTwo`, `pairEncode_size` — fan-in is preserved
  and buffering adds exactly one free-input vertex per input bit.

## Deviations from the source

The book's hard-wiring preserves size; explicitly buffering the doubled first
component adds `n` vertices. The overhead is polynomial and independent of the
contents of the fixed word. Copies remain distinct vertices, preserving the
model's requirement that a gate does not read the same vertex twice.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.6, Theorem 7.17; §6.3, Theorem 6.18.)
-/

namespace BoolCircuit

/-- A source input is copied by a singleton `∧`; a fixed bit is supplied by a constant. -/
def inputGate {n : ℕ} : Fin n ⊕ Bool → DAGGate
  | .inl i => ⟨.and, [i.val]⟩
  | .inr b => constGate b

/-- One buffer gate for each original input vertex. -/
def inputBuffer {n m : ℕ} (s : Fin m → Fin n ⊕ Bool) : List DAGGate :=
  List.ofFn fun i => inputGate (s i)

/-- The original inputs supplied by the free input vector and fixed source bits. -/
def inputValues {n m : ℕ} (s : Fin m → Fin n ⊕ Bool) (x : Fin n → Bool) :
    Fin m → Bool := fun i =>
  match s i with
  | .inl j => x j
  | .inr b => b

/-- A buffer gate reads only free input vertices. -/
theorem inputGate_args_lt {n : ℕ} (s : Fin n ⊕ Bool) :
    ∀ a ∈ (inputGate s).args, a < n := by
  cases s with
  | inl i =>
      intro a ha
      simp only [inputGate, List.mem_singleton] at ha
      subst a
      exact i.isLt
  | inr b =>
      intro a ha
      simp [inputGate] at ha

/-- Replace each original input by a distinct copy or constant vertex, then shift
every original gate and its output by the number of free inputs.

**Proof sketch.** Buffer gates read only the `n` free inputs. Each original
gate has all of its vertex numbers shifted by `n`, so its earlier-vertex
inequalities remain valid after the `m` buffer gates. The output is shifted
by the same amount and remains within the enlarged circuit. -/
def DAGCircuit.bufferInputs {n m : ℕ} (C : DAGCircuit m)
    (s : Fin m → Fin n ⊕ Bool) : DAGCircuit n where
  gates := inputBuffer s ++ C.gates.map (DAGGate.remap fun v => n + v)
  output := n + C.output
  args_lt := by
    intro i hi a ha
    have hlen : (inputBuffer s).length = m := by simp [inputBuffer]
    by_cases him : i < m
    · rw [List.getElem_append_left (by rw [hlen]; exact him)] at ha
      have hargs := inputGate_args_lt (s ⟨i, him⟩) a
        (by simpa [inputBuffer] using ha)
      omega
    · rw [List.getElem_append_right (by rw [hlen]; omega)] at ha
      simp only [List.getElem_map, DAGGate.remap, List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      have hiC : i - (inputBuffer s).length < C.gates.length := by
        simp only [List.length_append, List.length_map, hlen] at hi
        omega
      have hargs := C.args_lt (i - (inputBuffer s).length) hiC b hb
      omega
  output_lt := by
    have houtput := C.output_lt
    simp only [List.length_append, List.length_map, inputBuffer, List.length_ofFn]
    omega

/-- Buffer gate `i` evaluates to its selected source input bit or constant. -/
theorem inputBuffer_value {n m : ℕ}
    (s : Fin m → Fin n ⊕ Bool) (x : Fin n → Bool) (i : Fin m) :
    (runWith DAGGate.eval (inputBuffer s) (List.ofFn x)).getD
      (n + i.val) false = inputValues s x i := by
  have hi : i.val < (inputBuffer s).length := by
    simpa [inputBuffer] using i.isLt
  have hg := runWith_getD_gate DAGGate.eval (inputBuffer s) (List.ofFn x) hi false
  simp only [List.length_ofFn] at hg
  rw [hg]
  have hgate : (inputBuffer s)[i.val] = inputGate (s i) := by
    simp [inputBuffer]
  rw [hgate]
  cases hsi : s i with
  | inl j =>
      simpa [inputGate, DAGGate.eval, inputValues, hsi,
        List.getD_eq_getD_getElem?, j.isLt] using
        (runWith_getD_of_lt DAGGate.eval ((inputBuffer s).take i.val)
          (List.ofFn x) (v := j.val) (by simpa using j.isLt) false)
  | inr b =>
      simp [inputGate, inputValues, hsi]

/-- Buffered inputs preserve the original circuit's value on the supplied input vector.

**Proof sketch.** Each buffer vertex holds its selected input or constant. Shift every
original vertex by `n`; gate evaluation commutes with this renaming, so the shifted
output has the original output's value. -/
theorem DAGCircuit.bufferInputs_eval {n m : ℕ}
    (C : DAGCircuit m) (s : Fin m → Fin n ⊕ Bool) (x : Fin n → Bool) :
    (C.bufferInputs s).eval x = C.eval (inputValues s x) := by
  have key := runWith_remap_rel DAGGate.eval Eq false (fun v => n + v)
    (fun g _ _ h => DAGGate.eval_remap g _ h)
    (L := m) (L' := n + m)
    (List.ofFn (inputValues s x))
    (runWith DAGGate.eval (inputBuffer s) (List.ofFn x))
    (by simp)
    (by simp [inputBuffer])
    (fun v hv => by simp only []; omega)
    (fun i => by simp only []; omega)
    (fun v hv => by
      simpa [List.getD_eq_getD_getElem?, hv] using inputBuffer_value s x ⟨v, hv⟩)
    C.gates C.args_lt C.output C.output_lt
  unfold DAGCircuit.eval DAGCircuit.values DAGCircuit.bufferInputs
  dsimp only
  rw [runWith_append]
  exact key

/-- Buffering inputs preserves well-formedness and fan-in at most two, and adds
exactly `n` vertices to the original circuit's size.

**Proof sketch.** Each buffer is either a singleton identity gate or a constant gate.
Shifting every old vertex number by `n` is injective, so it preserves distinct gate
inputs, gate kinds, and fan-in. There are `n` inputs, `m` buffer gates, and all
of the original gates. -/
theorem DAGCircuit.bufferInputs_structure {n m : ℕ} (C : DAGCircuit m)
    (s : Fin m → Fin n ⊕ Bool) (hC : C.IsFaninTwo) :
    (C.bufferInputs s).IsWellFormed ∧
      (C.bufferInputs s).IsFaninTwo ∧
      (C.bufferInputs s).size = n + C.size := by
  have hall : ∀ g ∈ (C.bufferInputs s).gates, g.FaninTwo := by
    intro g hg
    change g ∈ inputBuffer s ++ C.gates.map (DAGGate.remap (fun v => n + v)) at hg
    rcases List.mem_append.mp hg with hg | hg
    · change g ∈ List.ofFn (fun i => inputGate (s i)) at hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      cases hs : s i with
      | inl j =>
          simp [inputGate, hs, DAGGate.FaninTwo, DAGGate.WellFormed]
      | inr b =>
          simpa [inputGate, hs] using constGate_faninTwo b
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hnd, hnot⟩ := hC.1 g₀ hg₀
      refine ⟨⟨hnd.map (fun a b hab => Nat.add_left_cancel hab), ?_⟩, ?_⟩
      · intro h
        simpa [DAGGate.remap] using hnot h
      · simpa [DAGGate.remap] using hC.2 g₀ hg₀
  have hw : (C.bufferInputs s).IsWellFormed := fun g hg => (hall g hg).1
  refine ⟨hw, ⟨hw, fun g hg => (hall g hg).2⟩, ?_⟩
  simp [DAGCircuit.size, DAGCircuit.bufferInputs, inputBuffer, Nat.add_assoc]

/-- The doubled free-input sources, followed by the separator and fixed-word constants. -/
def pairWireList (n : ℕ) (r : List Bool) : List (Fin n ⊕ Bool) :=
  (List.ofFn (fun i : Fin n => Sum.inl i)).flatMap (fun s => [s, s]) ++
    ([false, true] ++ r).map Sum.inr

/-- The wire list has the paired input's length, and evaluating its sources produces
the self-delimiting encoding of the free input and fixed word.

**Proof sketch.** Mapping source values through a duplicated list duplicates their
values, by induction on that list. The remaining sources are constants supplying the
separator and fixed word. Taking lengths gives the stated size. -/
theorem pairWireList_spec (n : ℕ) (r : List Bool) :
    (pairWireList n r).length = 2 * n + 2 + r.length ∧
      ∀ v : Fin n → Bool,
        (pairWireList n r).map (fun s =>
          match s with
          | .inl i => v i
          | .inr b => b) = Turing.pairEncode (List.ofFn v) r := by
  have hdup (f : Fin n ⊕ Bool → Bool) (l : List (Fin n ⊕ Bool)) :
      (l.flatMap (fun s => [s, s])).map f =
        (l.map f).flatMap (fun b => [b, b]) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
        simp only [List.flatMap_cons, List.map_append, List.map_cons,
          List.map_nil, ih]
  have hmap (v : Fin n → Bool) :
      (pairWireList n r).map (fun s =>
        match s with
        | .inl i => v i
        | .inr b => b) = Turing.pairEncode (List.ofFn v) r := by
    unfold pairWireList
    rw [List.map_append, hdup]
    simp [Turing.pairEncode, List.map_map, Function.comp_def, List.append_assoc]
  refine ⟨?_, hmap⟩
  have hlen := congrArg List.length (hmap (fun _ => false))
  simpa only [List.length_map, Turing.length_pairEncode, List.length_ofFn] using hlen

/-- View a list of length `m` as a vector indexed by `Fin m`. -/
def vectorOfList {α : Type*} {m : ℕ} (l : List α) (h : l.length = m) :
    Fin m → α :=
  fun i => l.get (Fin.cast h.symm i)

/-- Turning a list into its indexed vector and back recovers the list. -/
@[simp] theorem vectorOfList_ofFn {α : Type*} {m : ℕ}
    (l : List α) (h : l.length = m) :
    List.ofFn (vectorOfList l h) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getElem_ofFn, vectorOfList, List.get_eq_getElem, Fin.coe_cast]

/-- The vector of source wires for the self-delimiting paired input. -/
def pairWiring (n : ℕ) (r : List Bool) : Fin (2 * n + 2 + r.length) → Fin n ⊕ Bool :=
  vectorOfList (pairWireList n r) (pairWireList_spec n r).1

/-- The input vector encoding the free word and the fixed second word. -/
def pairEncodeInput {n : ℕ} (r : List Bool) (v : Fin n → Bool) :
    Fin (2 * n + 2 + r.length) → Bool :=
  inputValues (pairWiring n r) v

/-- The circuit computing `C` on the self-delimiting pair of its free input and fixed
word `r`. This is the hard-wiring construction of [AB09, Thm 7.17], with explicit
copies for the doubled first component of the library's encoding. -/
def DAGCircuit.pairEncode {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) : DAGCircuit n :=
  C.bufferInputs (pairWiring n r)

/-- Converting the paired input vector to a word gives the exact library encoding. -/
theorem pairEncodeInput_ofFn {n : ℕ} (r : List Bool) (v : Fin n → Bool) :
    List.ofFn (pairEncodeInput r v) = Turing.pairEncode (List.ofFn v) r := by
  have e1 : List.ofFn (pairEncodeInput r v)
      = (List.ofFn (pairWiring n r)).map
          (fun s : Fin n ⊕ Bool => match s with | .inl j => v j | .inr b => b) := by
    rw [List.map_ofFn]
    rfl
  rw [e1]
  unfold pairWiring
  rw [vectorOfList_ofFn]
  exact (pairWireList_spec n r).2 v

/-- The paired circuit computes the original circuit on `pairEncode x r`, with `r`
fixed. This is the circuit step of [AB09, Thm 7.17]. -/
theorem DAGCircuit.pairEncode_eval {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) (v : Fin n → Bool) :
    (C.pairEncode r).eval v = C.eval (pairEncodeInput r v) :=
  C.bufferInputs_eval (pairWiring n r) v

/-- Encoding and fixing a word preserves fan-in at most two, as needed in
[AB09, Thm 7.17]. -/
theorem DAGCircuit.pairEncode_isFaninTwo {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) (hC : C.IsFaninTwo) :
    (C.pairEncode r).IsFaninTwo :=
  (C.bufferInputs_structure (pairWiring n r) hC).2.1

/-- Encoding and fixing a word preserves well-formedness for a fan-in-two circuit. -/
theorem DAGCircuit.pairEncode_isWellFormed {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) (hC : C.IsFaninTwo) :
    (C.pairEncode r).IsWellFormed :=
  (C.bufferInputs_structure (pairWiring n r) hC).1

/-- Buffering an encoded input adds exactly `n` vertices. The overhead in the
hard-wiring step of [AB09, Thm 7.17] is independent of the fixed word's bits. -/
theorem DAGCircuit.pairEncode_size {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) :
    (C.pairEncode r).size = n + C.size := by
  simp [DAGCircuit.size, DAGCircuit.pairEncode, DAGCircuit.bufferInputs,
    inputBuffer, Nat.add_assoc]

/-- A circuit family's language contains a word formed from a vector exactly when
the circuit at that vector's length accepts the vector. -/
theorem DAGCircuitFamily.mem_language_ofFn {m : ℕ} (F : DAGCircuitFamily)
    (v : Fin m → Bool) :
    List.ofFn v ∈ F.language ↔ (F.circuit m).eval v = true := by
  have htuple :
      (⟨(List.ofFn v).length, (List.ofFn v).get⟩ :
        Σ k : ℕ, Fin k → Bool) = ⟨m, v⟩ :=
    List.equivSigmaTuple.right_inv ⟨m, v⟩
  exact (F.mem_language_iff (List.ofFn v)).trans
    (Iff.of_eq (congrArg
      (fun p : Σ k : ℕ, Fin k → Bool =>
        (F.circuit p.1).eval p.2 = true) htuple))

/-- Acceptance of an encoded input vector is membership of the exact paired word in
the circuit family's language. This avoids index casts in [AB09, Thm 7.17]'s use of
the polynomial-size family. -/
theorem DAGCircuitFamily.pairEncode_eval_eq_true_iff {n : ℕ}
    (F : DAGCircuitFamily) (r : List Bool) (v : Fin n → Bool) :
    (F.circuit (2 * n + 2 + r.length)).eval (pairEncodeInput r v) = true ↔
      Turing.pairEncode (List.ofFn v) r ∈ F.language :=
  (F.mem_language_ofFn (pairEncodeInput r v)).symm.trans
    (Iff.of_eq (congrArg (fun w : List Bool => w ∈ F.language)
      (pairEncodeInput_ofFn r v)))

end BoolCircuit
