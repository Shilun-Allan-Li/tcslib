/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGCircuitSat
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.ClassNP.SAT

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CKT-SAT as a language of strings, and Lemma 6.11 at the string level

[AB09, Def 6.9] defines CKT-SAT as a language of *strings representing* circuits.  This
file makes `BoolCircuit.dagCktSat` (`DAGCircuitSat.lean`) a `Language Bool` through the
circuit description `BoolCircuit.DAGCircuit.encode` of `Uniform.lean`, writes a decoder
for that description, and composes it with the Tseitin formula and the campaign's CNF
serialization `Std.Sat.CNF.serialize` into an explicit total map
`f = dagCktSatToSAT3 : List Bool → List Bool` that is a many-one map:
`w ∈ CKT-SAT ↔ f w ∈ Complexity.SAT3` (the campaign's 3SAT).

## Main definitions

* `BoolCircuit.DAGCircuit.decode` — the decoder for `DAGCircuit.encode`.
* `BoolCircuit.dagCktSatLang` — CKT-SAT: descriptions of satisfiable fan-in-two
  circuits.  [AB09, Def 6.9]
* `BoolCircuit.dagCktSatToSAT3` — the string map of [AB09, Lem 6.11]: decode, build the
  Tseitin 3-CNF, serialize; anything that is not the description of a fan-in-two
  circuit goes to the serialization of the unsatisfiable formula with one empty clause.

## Main results

* `BoolCircuit.DAGCircuit.decode_encode`, `BoolCircuit.DAGCircuit.encode_of_decode` —
  the decoder inverts the description and accepts nothing else.
* `BoolCircuit.mem_dagCktSatLang_iff_decode` — membership through the decoder.
* `BoolCircuit.mem_dagCktSatLang_iff_mem_SAT3` — for every string `w`,
  `w ∈ CKT-SAT ↔ dagCktSatToSAT3 w ∈ 3SAT`.  [AB09, Lem 6.11], equisatisfiability.

## Divergences from [AB09, §6.1.2]

* **The `≤p` claim is in `CircuitSatReduction.lean`.**  The string map is explicit and
  total, and maps CKT-SAT onto 3SAT exactly; that it is computable in polynomial time by
  a Turing machine (`Complexity.PolyTimeComputable`) is
  `BoolCircuit.polyTimeComputable_dagCktSatToSAT3`, and `CKT-SAT ≤p 3SAT` is
  `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3`, both in `CircuitSatReduction.lean`
  (which imports this file).
* **The circuit description** is `DAGCircuit.encode` (unary numbers, see `Uniform.lean`),
  not the adjacency matrix sketched on [AB09, p. 112]; for fan-in-two circuits its length
  is polynomial in the size (`DAGCircuit.length_encode_le_of_isFaninTwo`).
* **Malformed strings are outside CKT-SAT** (every string not describing a fan-in-two
  circuit), and are mapped to the serialization of `[[]]` (one empty clause): a width-`0`
  — hence 3-CNF — formula that is unsatisfiable, so outside `Complexity.SAT3`.  (The
  campaign's `CNF.decode` fallback is the *satisfiable* empty formula, so the map must
  not send malformed inputs to a malformed string.)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1.2, Definition 6.9 and Lemma 6.11, pp. 110–111.)
-/

namespace BoolCircuit

open Std.Sat (CNF)

/-! ## Decoding circuit descriptions -/

/-- Read a list code (`BoolCircuit.encodeList`) off the front of a string, reading each
element with `f`; `fuel` bounds the number of elements. -/
def decodeList {α : Type} (f : List Bool → Option (α × List Bool)) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: r => some ([], r)
  | fuel + 1, true :: r =>
    (f r).bind fun p => (decodeList f fuel p.2).map fun q => (p.1 :: q.1, q.2)

/-- Read a two-bit gate label (`BoolCircuit.GateKind.encode`) off the front of a string. -/
def GateKind.decode : List Bool → Option (GateKind × List Bool)
  | false :: false :: r => some (.and, r)
  | false :: true :: r => some (.or, r)
  | true :: false :: r => some (.not, r)
  | _ => none

/-- Read a gate code (`BoolCircuit.DAGGate.encode`) off the front of a string. -/
def DAGGate.decode (bs : List Bool) : Option (DAGGate × List Bool) :=
  (GateKind.decode bs).bind fun p =>
    (decodeList decodeNat p.2.length p.2).map fun q => (⟨p.1, q.1⟩, q.2)

/-- The circuit on `n` inputs with the given gates and output vertex, if these satisfy
the acyclicity and output-range conditions of `DAGCircuit`. -/
def DAGCircuit.ofParts (n : ℕ) (gates : List DAGGate) (output : ℕ) :
    Option (DAGCircuit n) :=
  haveI : Decidable (∀ (i : ℕ) (hi : i < gates.length), ∀ a ∈ (gates[i]).args, a < n + i) :=
    Nat.decidableBallLT _ _
  if h : (∀ (i : ℕ) (hi : i < gates.length), ∀ a ∈ (gates[i]).args, a < n + i) ∧
      output < n + gates.length then
    some ⟨gates, output, h.1, h.2⟩
  else none

/-- **The decoder** for circuit descriptions (`DAGCircuit.encode`): read the number of
inputs, the gate list and the output vertex, check the circuit conditions, and accept
only if the result re-encodes to the input string. -/
def DAGCircuit.decode (w : List Bool) : Option ((n : ℕ) × DAGCircuit n) :=
  (decodeNat w).bind fun p =>
    (decodeList DAGGate.decode p.2.length p.2).bind fun q =>
      (decodeNat q.2).bind fun o =>
        (DAGCircuit.ofParts p.1 q.1 o.1).bind fun C =>
          if C.encode = w then some ⟨p.1, C⟩ else none

/-- Reading back a list code returns the list and the untouched rest, given enough fuel
and an element reader inverting the element code.

**Proof sketch.** Induction on the list: the empty code is the stop bit; a nonempty code
is a continue bit, the head's code (read back by hypothesis, leaving the tail's code)
and the tail's code (read back by induction with one less unit of fuel). -/
theorem decodeList_encodeList {α : Type} (f : List Bool → Option (α × List Bool))
    (g : α → List Bool) (as : List α) (hf : ∀ a ∈ as, ∀ r, f (g a ++ r) = some (a, r))
    (fuel : ℕ) (hfuel : as.length < fuel) (r : List Bool) :
    decodeList f fuel (encodeList g as ++ r) = some (as, r) := by
  induction as generalizing fuel with
  | nil =>
    obtain ⟨fuel, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    simp [encodeList, decodeList]
  | cons a as ih =>
    obtain ⟨fuel, rfl⟩ : ∃ m, fuel = m + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have ha := hf a (by simp) (encodeList g as ++ r)
    have hs := ih (fun b hb => hf b (by simp [hb])) fuel (by simp at hfuel; omega)
    simp [encodeList, decodeList, List.append_assoc, ha, hs]

/-- Reading back a gate label returns it and the untouched rest. -/
theorem GateKind.decode_encode (k : GateKind) (r : List Bool) :
    GateKind.decode (k.encode ++ r) = some (k, r) := by
  cases k <;> rfl

/-- Reading back a gate code returns the gate and the untouched rest. -/
theorem DAGGate.decode_encode (g : DAGGate) (r : List Bool) :
    DAGGate.decode (g.encode ++ r) = some (g, r) := by
  have hl := length_encodeList_ge encodeNat g.args
  simp only [DAGGate.decode, DAGGate.encode, List.append_assoc, GateKind.decode_encode,
    Option.bind_some]
  rw [decodeList_encodeList decodeNat encodeNat g.args
    (fun a _ r => decodeNat_encodeNat a r) _ (by simp; omega)]
  rfl

/-- `ofParts` rebuilds a circuit from its own gates and output. -/
theorem DAGCircuit.ofParts_self {n : ℕ} (C : DAGCircuit n) :
    DAGCircuit.ofParts n C.gates C.output = some C := by
  rw [DAGCircuit.ofParts, dif_pos ⟨C.args_lt, C.output_lt⟩]

/-- The decoder inverts the description: `decode (encode C) = some C`.

**Proof sketch.** Read back, in turn, the unary number of inputs, the gate list (each
gate by `DAGGate.decode_encode`, with fuel the remaining length, which exceeds the
number of gates) and the unary output vertex; the parts satisfy the circuit conditions
because they come from a circuit, and the result re-encodes to the input. -/
theorem DAGCircuit.decode_encode {n : ℕ} (C : DAGCircuit n) :
    DAGCircuit.decode C.encode = some ⟨n, C⟩ := by
  have hl := length_encodeList_ge DAGGate.encode C.gates
  unfold DAGCircuit.decode
  conv_lhs => enter [1]; rw [DAGCircuit.encode, decodeNat_encodeNat]
  simp only [Option.bind_some]
  rw [decodeList_encodeList DAGGate.decode DAGGate.encode C.gates
    (fun g _ r => DAGGate.decode_encode g r) _ (by simp; omega)]
  simp only [Option.bind_some]
  rw [show encodeNat C.output = encodeNat C.output ++ [] by simp, decodeNat_encodeNat]
  simp [DAGCircuit.ofParts_self]

/-- The decoder accepts only descriptions: `decode w = some C` implies `encode C = w`. -/
theorem DAGCircuit.encode_of_decode {w : List Bool} {C : (n : ℕ) × DAGCircuit n}
    (h : DAGCircuit.decode w = some C) : C.2.encode = w := by
  simp only [DAGCircuit.decode, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, D, _, h⟩ := h
  split_ifs at h with hD
  cases h
  exact hD

/-! ## CKT-SAT as a language -/

/-- **CKT-SAT** [AB09, Def 6.9], as a language: the descriptions
(`DAGCircuit.encode`) of satisfiable fan-in-two circuits, i.e. the image of
`BoolCircuit.dagCktSat` under the description map. -/
def dagCktSatLang : Language Bool :=
  {w | ∃ C ∈ dagCktSat, C.2.encode = w}

/-- A string is in CKT-SAT iff it decodes to a circuit in `dagCktSat`. -/
theorem mem_dagCktSatLang_iff_decode (w : List Bool) :
    w ∈ dagCktSatLang ↔ ∃ C, DAGCircuit.decode w = some C ∧ C ∈ dagCktSat := by
  constructor
  · rintro ⟨⟨n, C⟩, hC, rfl⟩
    exact ⟨⟨n, C⟩, DAGCircuit.decode_encode C, hC⟩
  · rintro ⟨C, hd, hC⟩
    exact ⟨C, hC, DAGCircuit.encode_of_decode hd⟩

/-- The description of a circuit is in CKT-SAT iff the circuit is in `dagCktSat`. -/
theorem encode_mem_dagCktSatLang_iff {n : ℕ} (C : DAGCircuit n) :
    C.encode ∈ dagCktSatLang ↔ (⟨n, C⟩ : (n : ℕ) × DAGCircuit n) ∈ dagCktSat := by
  rw [mem_dagCktSatLang_iff_decode, DAGCircuit.decode_encode]
  simp

/-! ## The string map of Lemma 6.11 -/

/-- The formula the string map produces from a string: the Tseitin 3-CNF
(`DAGCircuit.toCNF`) of the circuit the string describes, if it describes a fan-in-two
circuit, and otherwise the unsatisfiable formula `[[]]` (one empty clause). -/
def dagCktSatToCNF (w : List Bool) : CNF ℕ :=
  match DAGCircuit.decode w with
  | some C => if C.2.IsFaninTwo then C.2.toCNF else [[]]
  | none => [[]]

/-- **The reduction map of [AB09, Lem 6.11] on strings**: decode the circuit, build its
Tseitin 3-CNF, and serialize it with the campaign's CNF serialization
(`Std.Sat.CNF.serialize`).  Strings not describing a fan-in-two circuit go to the
serialization of the unsatisfiable formula `[[]]`.  Its polynomial-time computability is
`BoolCircuit.polyTimeComputable_dagCktSatToSAT3` (`CircuitSatReduction.lean`). -/
def dagCktSatToSAT3 (w : List Bool) : List Bool :=
  CNF.serialize (dagCktSatToCNF w)

/-- The fallback formula `[[]]` is a 3-CNF and is unsatisfiable. -/
private theorem not_mem_SAT3_serialize_nil :
    CNF.serialize [[]] ∉ Complexity.SAT3 := by
  rintro ⟨-, a, ha⟩
  simp [CNF.decode_serialize] at ha

/-- **[AB09, Lem 6.11], string level (equisatisfiability)**: for every string `w`, `w`
describes a satisfiable fan-in-two circuit iff `dagCktSatToSAT3 w` is in the campaign's
`3SAT` (`Complexity.SAT3`: decodes to a satisfiable formula with at most three literals
per clause).  This is the correctness half of `CKT-SAT ≤p 3SAT`; with the polynomial-time
computability of `dagCktSatToSAT3` it gives `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3`
(`CircuitSatReduction.lean`).

**Proof sketch.** `Std.Sat.CNF.decode` inverts `serialize`, so the right side says the
produced formula is a satisfiable 3-CNF.  If `w` decodes to a fan-in-two circuit `C`,
then `w ∈ CKT-SAT` iff `C` is satisfiable (the decoder accepts only descriptions), and
the Tseitin formula is a 3-CNF which is satisfiable iff `C` is
(`mem_dagCktSat_iff_toCNF`).  Otherwise `w` describes no fan-in-two circuit, so it is
outside CKT-SAT, and the produced formula `[[]]` is unsatisfiable. -/
theorem mem_dagCktSatLang_iff_mem_SAT3 (w : List Bool) :
    w ∈ dagCktSatLang ↔ dagCktSatToSAT3 w ∈ Complexity.SAT3 := by
  rw [mem_dagCktSatLang_iff_decode, dagCktSatToSAT3, dagCktSatToCNF]
  cases hd : DAGCircuit.decode w with
  | none =>
    simp only [reduceCtorEq, false_and, exists_false, false_iff]
    exact not_mem_SAT3_serialize_nil
  | some C =>
    simp only [Option.some.injEq, exists_eq_left']
    split_ifs with hC
    · rw [mem_dagCktSat_iff_toCNF C hC]
      change _ ↔ (CNF.decode _).WidthAtMost 3 ∧ (CNF.decode _).Satisfiable
      rw [CNF.decode_serialize]
    · simp only [mem_dagCktSat_iff, hC, false_and, false_iff]
      exact not_mem_SAT3_serialize_nil

/-! Sanity checks: the one-input circuit `¬x₀` is in CKT-SAT, the one-input circuit
`x₀ ∧ ¬x₀` is not, and the empty string describes no circuit. -/

/-- The circuit `¬x₀` on one input. -/
private def notCircuit : DAGCircuit 1 where
  gates := [⟨.not, [0]⟩]
  output := 1
  args_lt := by
    intro i hi a ha
    simp at hi
    subst hi
    simp at ha
    omega
  output_lt := by simp

/-- The circuit `x₀ ∧ ¬x₀` on one input. -/
private def contraCircuit : DAGCircuit 1 where
  gates := [⟨.not, [0]⟩, ⟨.and, [0, 1]⟩]
  output := 2
  args_lt := by
    intro i hi a ha
    match i, hi with
    | 0, _ => simp at ha; omega
    | 1, _ => simp at ha; omega
  output_lt := by simp

example : notCircuit.encode ∈ dagCktSatLang := by
  rw [encode_mem_dagCktSatLang_iff, mem_dagCktSat_iff]
  refine ⟨by decide, fun _ => false, by decide⟩

example : contraCircuit.encode ∉ dagCktSatLang := by
  rw [encode_mem_dagCktSatLang_iff, mem_dagCktSat_iff]
  rintro ⟨-, x, hx⟩
  revert hx
  cases h : x 0 <;> decide +revert

example : ([] : List Bool) ∉ dagCktSatLang := by
  rw [mem_dagCktSatLang_iff_decode]
  rintro ⟨C, hd, -⟩
  simp [DAGCircuit.decode, decodeNat] at hd

end BoolCircuit
