/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.CounterProgSimRun
import TCSlib.Complexity.CircuitComplexity.LogspaceTableauFront
import TCSlib.Complexity.CircuitComplexity.UniformTableau
import TCSlib.Complexity.CircuitComplexity.LogspaceUniform

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logspace-uniform circuits for languages in P

[AB09, Remark 6.7]: the circuit simulating a polynomial-time machine "can also be computed
in polynomial time, and even in logarithmic space"; and [AB09, Thm 6.15]: "a language has
logspace-uniform circuits of polynomial size iff it is in P".

The family is the uniform configuration tableau `Complexity.tabFamily M C d`
(`UniformTableau.lean`). Its description is printed by the counter program
`Complexity.UTab.prog M` (the emitter) run on `1ⁿ 0 1ᵀ 0`, which is itself printed from `1ⁿ`
by the counter program `Complexity.UTab.Front.prog C d`. Both run for polynomially many steps,
so their registers have `O(log n)` bits, and each bit of the composed output is recomputed on
demand by an abstract register machine (`Complexity.UnaryLogspace.counterProg`, applied
twice, starting from `n ↦ 1ⁿ`, `Complexity.unaryLogspace_replicate`).

## Main results

* `Complexity.tabFamily_isLogspaceUniform` — the tableau family is logspace-uniform.
  [AB09, Remark 6.7, logarithmic-space half]
* `Language.exists_isLogspaceUniform_of_mem_P` — every `L ∈ P` is decided by a
  logspace-uniform family of polynomial-size fan-in-two circuits.
* `Language.mem_P_iff_exists_isLogspaceUniform` — [AB09, Thm 6.15].

## Divergences from [AB09]

* **The circuit.** [AB09, Remark 6.7] argues logspace-computability for the circuit of
  Thm 6.6's proof built from an *oblivious* machine, whose head positions at each step are
  logspace computable. The family here is the non-oblivious configuration tableau of
  `UniformTableau.lean` (`O(T (T + n))` gates for `T` steps), whose wiring is a regular grid
  needing no schedule; logspace-computability is proved for it, not for the oblivious
  circuit.
* **The proof.** Instead of addressing bits of the description by closed-form arithmetic, the
  polynomial-time emitter (a counter program) is simulated with binary registers, stopping
  at the requested bit — the composition argument of [AB09, Lemma 4.17] specialised to an
  outer function computed with polynomially bounded counters.
* **Fan-in two and polynomial size** are explicit in the statement of Thm 6.15
  (`DAGCircuitFamily.HasFaninTwo`, `DAGCircuitFamily.IsPolySize`): the circuit model allows
  unbounded fan-in; polynomial size also follows from logspace-uniformity
  (`DAGCircuitFamily.IsLogspaceUniform.isPolySize`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Lemma 4.17; §6.1, Theorem 6.6, Remark 6.7;
  §6.2.1, Definition 6.14, Theorem 6.15.)
-/

namespace Complexity

open Turing BoolCircuit

/-- **The emitter's input is unary-logspace**: `n ↦ 1ⁿ 0 1ᵀ 0`, `T = (C + 1)(n + 1)^d`.

**Proof sketch.** It is the output of the front-end counter program on `1ⁿ`
(`UTab.Front.run_word`), and `n ↦ 1ⁿ` is unary-logspace. -/
theorem unaryLogspace_frontWord (C d : ℕ) : UnaryLogspace (UTab.Front.word C d) :=
  UnaryLogspace.counterProg (UTab.Front.prog C d) .rN unaryLogspace_replicate
    (UTab.Front.bnd C d) (d + 1) fun n => UTab.Front.run_word n

variable (M : FinTM Bool)

/-- The emitter halts on `1ⁿ 0 1ᵀ 0` within `emitC · (C + 4)³ (n + 1)^{3(d + 1)}` steps,
printing the description of the `n`-th tableau circuit.

**Proof sketch.** `UTab.goes_any` and `UTab.run_budget` give the halting run within
`emitC (|w| + 1)³` steps on `w = 1ⁿ 0 1ᵀ 0`; `|w| + 1 ≤ (C + 4)(n + 1)^{d+1}` bounds the time;
`UTab.tabEmit_eq` (with `T ≥ 1`) identifies the output as the description. -/
theorem emit_run (C d n : ℕ) : ∃ t ≤ UTab.emitC M * (C + 4) ^ 3 * (n + 1) ^ (3 * (d + 1)),
    (CounterProg.run (UTab.prog M) (UTab.Front.word C d n) (CounterProg.init .rN) t).lbl = none ∧
    (CounterProg.run (UTab.prog M) (UTab.Front.word C d n) (CounterProg.init .rN) t).out =
      ((tabFamily M C d).circuit n).encode := by
  set w := UTab.Front.word C d n with hw
  obtain ⟨ρ, p, e, B, hB, h⟩ := UTab.goes_any M w
  have hrun := UTab.run_budget M h hB
  refine ⟨UTab.emitC M * (w.length + 1) ^ 3, ?_, by rw [hrun], ?_⟩
  · have hY : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have hlen : w.length + 1 ≤ (C + 4) * (n + 1) ^ (d + 1) := by
      simp only [hw, UTab.Front.word, UTab.Front.tb, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil, pow_succ]
      have h1 : (C + 1) * (n + 1) ^ d ≤ (C + 1) * (n + 1) ^ d * (n + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      have h2 : n + 1 ≤ (n + 1) ^ d * (n + 1) := Nat.le_mul_of_pos_left _ hY
      have e : (C + 4) * ((n + 1) ^ d * (n + 1)) =
          (C + 1) * (n + 1) ^ d * (n + 1) + 3 * ((n + 1) ^ d * (n + 1)) := by ring
      rw [e]; omega
    calc UTab.emitC M * (w.length + 1) ^ 3
        ≤ UTab.emitC M * ((C + 4) * (n + 1) ^ (d + 1)) ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen 3)
      _ = UTab.emitC M * (C + 4) ^ 3 * (n + 1) ^ (3 * (d + 1)) := by ring
  · have := UTab.tabEmit_eq M n (UTab.Front.tb C d n) []
      (Nat.one_le_iff_ne_zero.mpr (by unfold UTab.Front.tb; positivity))
    have hw' : w = List.replicate n true ++ false ::
        (List.replicate (UTab.Front.tb C d n) true ++ false :: []) := hw
    rw [← hw', UTab.tabEmit, hrun] at this
    rw [hrun]
    exact this

/-- **[AB09, Remark 6.7], logarithmic-space half: the tableau family is logspace-uniform** —
the map `1ⁿ ↦ (description of the n-th circuit)` is implicitly logspace computable.

The circuit is the non-oblivious configuration tableau, not the oblivious-machine circuit of
the book's argument (see the module docstring).

**Proof sketch.** The descriptions are the outputs of the emitter on the front end's outputs
(`emit_run`); both counter programs run for polynomially many steps, so
`UnaryLogspace.counterProg` (twice) makes the descriptions unary-logspace, and their length
is polynomial (`CounterProg.length_out_le`); `UnaryLogspace.implicitlyLogspaceComputable`
gives the uniformity function `unaryExt`. -/
theorem tabFamily_isLogspaceUniform (C d : ℕ) : (tabFamily M C d).IsLogspaceUniform := by
  set g : ℕ → List Bool := fun n => ((tabFamily M C d).circuit n).encode with hg
  have hrun := emit_run M C d
  have hU : UnaryLogspace g :=
    UnaryLogspace.counterProg (UTab.prog M) .rN (unaryLogspace_frontWord C d) _ _ hrun
  have hlen : ∃ C' c' : ℕ, ∀ n, (g n).length ≤ C' * (n + 1) ^ c' := by
    refine ⟨(UTab.emitC M * (C + 4) ^ 3 + 1) ^ 2, 2 * (3 * (d + 1)), fun n => ?_⟩
    obtain ⟨t, ht, -, hout⟩ := hrun n
    show (((tabFamily M C d).circuit n).encode).length ≤ _
    rw [← hout]
    exact CounterProg.length_out_le _ _ _ _ _ _ _ ht
  exact ⟨unaryExt g, hU.implicitlyLogspaceComputable hlen, fun n => unaryExt_replicate g n⟩

end Complexity

open Complexity in
/-- **[AB09, Remark 6.7] / Thm 6.15, "only if": languages in `P` have logspace-uniform
circuits.** Every `L ∈ P` is decided by a logspace-uniform family of polynomial-size fan-in-two
circuits (the tableau family of a polynomial-time decider). -/
theorem Language.exists_isLogspaceUniform_of_mem_P {L : Language Bool} (hL : L ∈ Complexity.P) :
    ∃ C : BoolCircuit.DAGCircuitFamily,
      C.IsLogspaceUniform ∧ C.IsPolySize ∧ C.HasFaninTwo ∧ C.language = L := by
  obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp hL
  exact ⟨tabFamily M C d, tabFamily_isLogspaceUniform M C d,
    (tabFamily_isLogspaceUniform M C d).isPolySize, tabFamily_hasFaninTwo M C d,
    tabFamily_language M hM⟩

/-- **[AB09, Thm 6.15]: a language has logspace-uniform circuits of polynomial size iff it is
in `P`.**

Divergences: fan-in two (part of [AB09, Def 6.1]) is explicit, the circuit model allowing
unbounded fan-in; polynomial size is stated although it follows from logspace-uniformity.

**Proof sketch.** "If": logspace-uniform families are P-uniform
(`DAGCircuitFamily.IsLogspaceUniform.isPUniform`), and P-uniform fan-in-two families decide
languages in `P` (`Language.mem_P_of_isPUniform`). "Only if":
`Language.exists_isLogspaceUniform_of_mem_P`. -/
theorem Language.mem_P_iff_exists_isLogspaceUniform (L : Language Bool) :
    L ∈ Complexity.P ↔ ∃ C : BoolCircuit.DAGCircuitFamily,
      C.IsLogspaceUniform ∧ C.IsPolySize ∧ C.HasFaninTwo ∧ C.language = L :=
  ⟨Language.exists_isLogspaceUniform_of_mem_P,
    fun ⟨C, hU, _, hF, hL⟩ => Language.mem_P_of_isPUniform C hU.isPUniform hF hL⟩
