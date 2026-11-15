/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitEvalCorrect
import TCSlib.Complexity.CircuitComplexity.CircuitEvalRun
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Evaluating a circuit is in polynomial time

[AB09] uses, in the proofs of Theorems 6.13, 6.18 and 6.19 and for "CKT-SAT is clearly in
NP" (p. 111), that given a circuit and an input one can compute the circuit's output in
polynomial time. This file proves it for the book's circuit model
`BoolCircuit.DAGCircuit` (fan-in two) and the circuit description
`BoolCircuit.DAGCircuit.encode`: the *circuit-value language*

  `CVAL = { ⟨C, x⟩ | C a fan-in-two circuit on |x| inputs with C(x) = 1 }`

is in the campaign's class `Complexity.P`, decided by the two-work-tape binary machine
`BoolCircuit.CircuitEval.evalTM` in `12 · (m + 1)²` steps on inputs of length `m`.

The development is split as follows: `CircuitEvalSpec.lean` (the streaming algorithm as
a finite action table and an abstract run), `CircuitEvalCorrect.lean` (the abstract run
accepts exactly the descriptions of fan-in-two circuits with output `1`),
`CircuitEvalMachine.lean` (the machine and the simulation of the main pass),
`CircuitEvalRun.lean` (setup, rejection of malformed strings, the timed run), this file
(the languages and their membership in `P`), and `CircuitEvalNP.lean` (CKT-SAT ∈ NP).

## Main definitions

* `BoolCircuit.CVAL` — the circuit-value language: `Turing.pairEncode C.encode x` for
  fan-in-two circuits `C : DAGCircuit |x|` with `C.eval x = 1`.
* `BoolCircuit.CVALPrefix` — the variant with `n ≤ |x|` inputs, evaluated on the first
  `n` bits of `x` (the verifier of `CircuitEvalNP.lean`).

## Main results

* `BoolCircuit.CircuitEval.evalTM_decidesInTime_CVAL` — the machine decides `CVAL` within
  `12 · (m + 1)²` steps.
* `BoolCircuit.CVAL_mem_P`, `BoolCircuit.CVALPrefix_mem_P` — the circuit-value languages are
  in `P`.

## Divergences from [AB09]

* **The input pairs the description with the input** through `Turing.pairEncode`
  (description first, bits doubled); [AB09] leaves the pairing of `⟨C, x⟩` unspecified.
  Strings that are not of this form, or whose first component is not the description
  of a fan-in-two circuit on `|x|` inputs, are outside `CVAL` (and are rejected).
* **Fan-in two** (`DAGCircuit.IsFaninTwo`, which includes well-formedness: distinct
  arguments, `¬` gates with one argument) is part of the language, as in [AB09, Def 6.1];
  the machine checks it. The bound `12 (m + 1)²` is not optimized: a unary vertex index
  is walked on the value tape, which costs a factor of the input length per gate.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.1–§6.2; p. 111, Theorems 6.13, 6.18, 6.19.)
-/

namespace BoolCircuit

/-- **The circuit-value language** [AB09, p. 111; used in Thms 6.13, 6.18, 6.19]: the
pairs `⟨C, x⟩ = Turing.pairEncode C.encode x` of a fan-in-two circuit
`C : DAGCircuit |x|` and an input `x` on which `C` outputs `1`. -/
def CVAL : Language Bool :=
  {z | ∃ (x : List Bool) (C : DAGCircuit x.length), C.IsFaninTwo ∧ C.eval x.get = true ∧
    z = Turing.pairEncode C.encode x}

/-- The circuit-value language on a prefix of the input: the pairs
`Turing.pairEncode C.encode x` of a fan-in-two circuit `C` on `n ≤ |x|` inputs and a
string `x` whose first `n` bits make `C` output `1`. This is the verification language of
CKT-SAT (`CircuitEvalNP.lean`), where certificates are padded assignments. -/
def CVALPrefix : Language Bool :=
  {z | ∃ (x : List Bool) (n : ℕ) (C : DAGCircuit n), C.IsFaninTwo ∧ n ≤ x.length ∧
    C.eval (fun i => x.getD i false) = true ∧ z = Turing.pairEncode C.encode x}

/-- A string is in `CVAL` iff the circuit-value algorithm (with `exact`: the number of
inputs must equal the input length) accepts it.

**Proof sketch.** Both directions go through the algorithm's correctness
`CircuitEval.verdict_pairEncode`; a string with a `true` verdict is a pair
(`pairDecode` succeeds, so it is `pairEncode code x`), and `exact` forces the circuit's
number of inputs to be `|x|`, where `x.get` and `fun i => x.getD i false` agree. -/
theorem mem_CVAL_iff (z : List Bool) : z ∈ CVAL ↔ CircuitEval.verdict true z = true := by
  constructor
  · rintro ⟨x, C, hfan, hev, rfl⟩
    refine (CircuitEval.verdict_pairEncode true C.encode x).mpr
      ⟨x.length, C, hfan, rfl, le_rfl, fun _ => rfl, ?_⟩
    have : (fun i : Fin x.length => x.getD i false) = x.get := by
      funext i; simp [List.getD_eq_getElem?_getD]
    rw [this]; exact hev
  · intro h
    cases hd : Turing.pairDecode z with
    | none => simp [CircuitEval.verdict, hd] at h
    | some p =>
      obtain ⟨code, x⟩ := p
      have hz := Turing.eq_pairEncode_of_pairDecode z code x hd
      rw [hz] at h
      obtain ⟨n, C, hfan, henc, -, hex, hev⟩ :=
        (CircuitEval.verdict_pairEncode true code x).mp h
      obtain rfl := hex rfl
      refine ⟨x, C, hfan, ?_, by rw [hz, henc]⟩
      have : (fun i : Fin x.length => x.getD i false) = x.get := by
        funext i; simp [List.getD_eq_getElem?_getD]
      rw [← this]; exact hev

/-- A string is in `CVALPrefix` iff the circuit-value algorithm without `exact` accepts
it.

**Proof sketch.** As for `mem_CVAL_iff`: a string with a `true` verdict is a pair, and
on pairs both sides are the algorithm's correctness `CircuitEval.verdict_pairEncode`. -/
theorem mem_CVALPrefix_iff (z : List Bool) :
    z ∈ CVALPrefix ↔ CircuitEval.verdict false z = true := by
  constructor
  · rintro ⟨x, n, C, hfan, hn, hev, rfl⟩
    exact (CircuitEval.verdict_pairEncode false C.encode x).mpr
      ⟨n, C, hfan, rfl, hn, fun h => absurd h (by simp), hev⟩
  · intro h
    cases hd : Turing.pairDecode z with
    | none => simp [CircuitEval.verdict, hd] at h
    | some p =>
      obtain ⟨code, x⟩ := p
      have hz := Turing.eq_pairEncode_of_pairDecode z code x hd
      rw [hz] at h
      obtain ⟨n, C, hfan, henc, hn, -, hev⟩ :=
        (CircuitEval.verdict_pairEncode false code x).mp h
      exact ⟨x, n, C, hfan, hn, hev, by rw [hz, henc]⟩

namespace CircuitEval

/-- The machine `evalTM exact` decides, within `12 · (m + 1)²` steps on inputs of length
`m`, any language whose members are exactly the strings with verdict `true`. -/
theorem decidesInTime_of_verdict (exact : Bool) (L : Language Bool)
    (hL : ∀ z, z ∈ L ↔ verdict exact z = true) :
    (evalTM exact).DecidesInTime L fun n => 12 * (n + 1) ^ 2 := by
  intro z
  have h : Turing.MultiTapeTM.indicator (L : Set (List Bool)) z = verdict exact z := by
    unfold Turing.MultiTapeTM.indicator
    by_cases hz : z ∈ L
    · rw [if_pos hz]; exact ((hL z).mp hz).symm
    · rw [if_neg hz]
      cases hv : verdict exact z
      · rfl
      · exact absurd ((hL z).mpr hv) hz
  rw [h]
  exact evalTM_computes exact z

/-- **The circuit-value machine decides `CVAL`** within `12 · (m + 1)²` steps on inputs
of length `m`. [AB09, p. 111] -/
theorem evalTM_decidesInTime_CVAL :
    (evalTM true).DecidesInTime CVAL fun n => 12 * (n + 1) ^ 2 :=
  decidesInTime_of_verdict true CVAL mem_CVAL_iff

end CircuitEval

/-- **Evaluating a circuit is in polynomial time**: `CVAL ∈ P`. [AB09, p. 111, and the
proofs of Theorems 6.13, 6.18, 6.19]

**Proof sketch.** `CircuitEval.evalTM_decidesInTime_CVAL`: the machine decides `CVAL`
within `12 (m + 1)²` steps (it computes the algorithm's verdict,
`CircuitEval.evalTM_computes`, which is membership in `CVAL` by `mem_CVAL_iff`, itself
the algorithm's correctness `CircuitEval.verdict_pairEncode`); conclude with
`Complexity.mem_P_iff`. -/
theorem CVAL_mem_P : CVAL ∈ Complexity.P :=
  Complexity.mem_P_iff.mpr ⟨12, 2, _, CircuitEval.evalTM_decidesInTime_CVAL⟩

/-- The circuit-value language on a prefix of the input, `CVALPrefix`, is in `P`. -/
theorem CVALPrefix_mem_P : CVALPrefix ∈ Complexity.P :=
  Complexity.mem_P_iff.mpr
    ⟨12, 2, _, CircuitEval.decidesInTime_of_verdict false CVALPrefix mem_CVALPrefix_iff⟩

end BoolCircuit
