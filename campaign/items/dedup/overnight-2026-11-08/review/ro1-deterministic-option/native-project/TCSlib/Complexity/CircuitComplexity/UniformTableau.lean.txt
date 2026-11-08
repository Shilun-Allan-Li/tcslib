/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitterMain
import TCSlib.Complexity.CircuitComplexity.PUniformP
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionValid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# P-uniform circuits for languages in P

[AB09, Remark 6.7]: "The circuit is not only of polynomial size but can also be computed in
polynomial time, and even in logarithmic space." — the circuit simulating a polynomial-time
machine is
*P-uniform*.  With it, the "only if" direction of [AB09, Thm 6.13]: every language in `P` is
decided by a P-uniform family of circuits; with the accepted converse
(`Language.mem_P_of_isPUniform`, `PUniformP.lean`) this is the full characterization
`L ∈ P ↔ L` has P-uniform circuits.

The family is the uniform configuration tableau `Complexity.cfgTab M n [] T(n)` of a decider
`M` (`UniformTableauSpec.lean`), and its uniformity machine is the counter program of
`UniformTableauEmitter*.lean`, run on `1ⁿ 0 1^{T(n)} 0`; the input `1ⁿ` is first extended
by the (polynomial-time) unary time bound.

## Main definitions

* `Complexity.tabFamily M C d` — the circuits `cfgTab M n [] ((C + 1)(n + 1)^d)`.

## Main results

* `Complexity.tabFamily_isPUniform` — the family is P-uniform.  [AB09, Remark 6.7,
  polynomial-time half]
* `Complexity.tabFamily_language` — for a decider `M` of `L` within `C (n + 1)^d` steps, the
  family decides `L`.
* `Language.exists_isPUniform_of_mem_P` — every `L ∈ P` is decided by a P-uniform family of
  fan-in-two circuits.  [AB09, Thm 6.13, "only if"]
* `Language.mem_P_iff_exists_isPUniform` — `L ∈ P` iff `L` is decided by a P-uniform family
  of fan-in-two circuits.  [AB09, Thm 6.13]

## Divergences from [AB09]

* **The circuit.** [AB09] proves Thm 6.6 via an oblivious simulation; the uniform family
  here is the non-oblivious configuration tableau (the textbook Cook–Levin tableau), whose
  wiring is a regular grid and needs no schedule — the book's Remark 6.7 argues
  uniformity from the obliviousness schedule instead.  Its size is `O(T(T + n))` for a
  machine running in time `T`, so the family is polynomial-size.
* **Fan-in two** is part of the statement (the circuit model has it as a predicate,
  `DAGCircuitFamily.HasFaninTwo`), and the description is the library's unary encoding
  `DAGCircuit.encode` (see `Uniform.lean`).
* The logarithmic-space half of [AB09, Remark 6.7] and [AB09, Thm 6.15] are in
  `LogspaceTableau.lean` (`Complexity.tabFamily_isLogspaceUniform`,
  `Language.mem_P_iff_exists_isLogspaceUniform`): the emitter's counters are polynomially
  bounded, so it is simulated in logarithmic space with binary registers.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Theorem 6.6, Remark 6.7; §6.2, Theorem 6.13.)
-/

namespace Complexity

open Turing BoolCircuit

/-! ## The front end -/

/-- **The input of the emitter**: `1^{m(x)} 0 1^{T(x)} 0 z(x)`, polynomial-time computable
when its three parts are. -/
theorem polyTimeComputable_tabInput {m T z : List Bool → List Bool} (hm : PolyTimeComputable m)
    (hT : PolyTimeComputable T) (hz : PolyTimeComputable z) :
    PolyTimeComputable fun x => m x ++ false :: (T x ++ false :: z x) := by
  have := hm.append ((polyTimeComputable_const [false]).append
    (hT.append ((polyTimeComputable_const [false]).append hz)))
  simpa using this

/-! ## The uniform family -/

variable (M : FinTM Bool)

/-- **The uniform tableau family** of a machine `M` for the time bound `(C + 1)(n + 1)^d`: the
`n`-th circuit is `Complexity.cfgTab M n [] ((C + 1)(n + 1)^d)` (no hard-wired bits). -/
noncomputable def tabFamily (C d : ℕ) : DAGCircuitFamily :=
  ⟨fun n => cfgTab M n [] ((C + 1) * (n + 1) ^ d)⟩

/-- **[AB09, Remark 6.7], polynomial-time half: the tableau family is P-uniform** — the map
`1ⁿ ↦ (description of the n-th circuit)` is polynomial-time computable.

**Proof sketch.** It is the emitter (`Complexity.UTab.polyTimeComputable_tabEmit`) after the
front end `1ⁿ ↦ 1ⁿ 0 1^{(C + 1)(n + 1)^d} 0`; on this input the emitter prints the
description of `cfgTab M n [] ((C + 1)(n + 1)^d)` (`Complexity.UTab.tabEmit_eq`, the time
bound being at least `1`). -/
theorem tabFamily_isPUniform (C d : ℕ) : (tabFamily M C d).IsPUniform := by
  refine ⟨UTab.tabEmit M ∘ fun x => x ++ false ::
      (List.replicate ((C + 1) * (x.length + 1) ^ d) true ++ false :: []),
    (UTab.polyTimeComputable_tabEmit M).comp (polyTimeComputable_tabInput polyTimeComputable_id
      (polyTimeComputable_polyUnary (C + 1) d) (polyTimeComputable_const [])), fun n => ?_⟩
  simp only [Function.comp_apply, List.length_replicate]
  rw [UTab.tabEmit_eq M n _ [] (Nat.one_le_iff_ne_zero.mpr (by positivity))]
  rfl

/-- The tableau family has fan-in two. -/
theorem tabFamily_hasFaninTwo (C d : ℕ) : (tabFamily M C d).HasFaninTwo :=
  fun n => cfgTab_isFaninTwo M n [] _

/-- **The tableau family of a decider decides its language**: if `M` decides `L` within
`C (n + 1)^d` steps, the family `tabFamily M C d` decides `L`.

**Proof sketch.** The circuit outputs `1` iff some step before `(C + 1)(n + 1)^d` emits `1`
(`Complexity.cfgTab_eval`); since `M` halts within `C (n + 1)^d` steps with output the answer
bit, this is membership in `L` (`Complexity.decide_emits_eq_of_computesInTime`). -/
theorem tabFamily_language {L : Language Bool} {C d : ℕ}
    (hM : M.DecidesInTime L fun n => C * (n + 1) ^ d) : (tabFamily M C d).language = L := by
  ext w
  simp only [DAGCircuitFamily.mem_language_iff, tabFamily]
  rw [cfgTab_eval, List.nil_append, List.ofFn_get,
    decide_emits_eq_of_computesInTime ((hM w).mono (Nat.mul_le_mul_right _ (Nat.le_succ C)))]
  unfold MultiTapeTM.indicator
  by_cases h : w ∈ L <;> simp [h]

end Complexity

open Complexity in
/-- **[AB09, Thm 6.13], "only if" direction: languages in `P` have P-uniform circuits.** Every
`L ∈ P` is decided by a P-uniform family of fan-in-two circuits (`tabFamily` of a
polynomial-time decider of `L`).

**Proof sketch.** Take a decider `M` of `L` within `C (n + 1)^d` steps (`Complexity.mem_P_iff`);
its tableau family is P-uniform (`Complexity.tabFamily_isPUniform`), fan-in two, and
decides `L` (`Complexity.tabFamily_language`). -/
theorem Language.exists_isPUniform_of_mem_P {L : Language Bool} (hL : L ∈ Complexity.P) :
    ∃ C : BoolCircuit.DAGCircuitFamily, C.IsPUniform ∧ C.HasFaninTwo ∧ C.language = L := by
  obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp hL
  exact ⟨tabFamily M C d, tabFamily_isPUniform M C d, tabFamily_hasFaninTwo M C d,
    tabFamily_language M hM⟩

/-- **[AB09, Thm 6.13]: a language is in `P` iff it is decided by a P-uniform family of
(fan-in-two) circuits.**  The "if" direction is `Language.mem_P_of_isPUniform`
(`PUniformP.lean`), the "only if" direction `Language.exists_isPUniform_of_mem_P`.

Divergence: fan-in two (part of [AB09, Def 6.1]) is explicit, as the circuit model
`BoolCircuit.DAGCircuit` allows unbounded fan-in. -/
theorem Language.mem_P_iff_exists_isPUniform (L : Language Bool) :
    L ∈ Complexity.P ↔
      ∃ C : BoolCircuit.DAGCircuitFamily, C.IsPUniform ∧ C.HasFaninTwo ∧ C.language = L :=
  ⟨Language.exists_isPUniform_of_mem_P,
    fun ⟨C, hU, hF, hL⟩ => Language.mem_P_of_isPUniform C hU hF hL⟩
