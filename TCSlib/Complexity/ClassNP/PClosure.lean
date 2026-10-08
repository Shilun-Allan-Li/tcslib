/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.CoNP
import TCSlib.Complexity.ClassNP.PolyTimePairing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Closure properties of `P`

The class `P` [AB09, Def 1.13] is closed under polynomial-time preimages (many-one
reductions), under the Boolean operations, and hence under Boolean functions of finitely
many tests. These facts are used tacitly throughout [AB09] (e.g. ch. 2, ch. 5, ch. 6); here
they are derived from the function class FP (`TCSlib.Complexity.ClassNP.PolyTimePairing`)
and the closure under complement (`Complexity.compl_mem_P`, `ClassNP/CoNP.lean`).

## Main results

* `Complexity.mem_P_iff_polyTimeComputable` — `V ∈ P` iff its one-bit indicator is in FP;
  `Complexity.mem_P_of_test`, `Complexity.test_of_mem_P` — the same for Boolean tests.
* `Complexity.preimage_mem_P` — `P` is closed under polynomial-time preimages.
* `Complexity.inter_mem_P`, `Complexity.union_mem_P`, `Complexity.empty_mem_P`,
  `Complexity.univ_mem_P` — Boolean closure.
* `Complexity.mem_P_of_atoms` — `P` is closed under Boolean functions of finitely many
  tests.
* `Complexity.lenEq_mem_P`, `lenLe_mem_P`, `lenEq_preimage_mem_P`, `lenLe_preimage_mem_P`
  — length comparisons are in `P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6, Definition 1.13; §2.2.)
-/

namespace Complexity

open Turing

/-! ### `P` and polynomial-time functions -/

/-- `V ∈ P` iff its singleton indicator `x ↦ [1_V(x)]` is polynomial-time computable. -/
theorem mem_P_iff_polyTimeComputable {V : Language Bool} :
    V ∈ P ↔ PolyTimeComputable (fun x => [MultiTapeTM.indicator V x]) := by
  constructor
  · intro h
    obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp h
    exact ⟨M, C, c, hM⟩
  · rintro ⟨M, C, c, hM⟩
    exact mem_P_iff.mpr ⟨C, c, M, hM⟩

/-- **`P` is closed under polynomial-time preimages**: if `V ∈ P` and `g` is
polynomial-time computable then `g⁻¹(V) ∈ P` (the decider of `V` run on `g x`). -/
theorem preimage_mem_P {V : Language Bool} {g : List Bool → List Bool} (hV : V ∈ P)
    (hg : PolyTimeComputable g) : g ⁻¹' V ∈ P :=
  mem_P_iff_polyTimeComputable.mpr ((mem_P_iff_polyTimeComputable.mp hV).comp hg)

/-- A language whose Boolean test is polynomial-time computable (as a one-bit output) is
in `P`. -/
theorem mem_P_of_test {b : List Bool → Bool} (h : PolyTimeComputable (fun z => [b z])) :
    {z | b z = true} ∈ P := by
  rw [mem_P_iff_polyTimeComputable]
  convert h using 2 with z
  by_cases hz : b z = true <;> simp [MultiTapeTM.indicator, hz]

/-- The Boolean test of a language in `P` is polynomial-time computable. -/
theorem test_of_mem_P {L : Language Bool} (h : L ∈ P) :
    PolyTimeComputable (fun z => [MultiTapeTM.indicator L z]) :=
  mem_P_iff_polyTimeComputable.mp h

/-! ### Boolean closure -/

/-- **`P` is closed under intersection.** -/
theorem inter_mem_P {L₁ L₂ : Language Bool} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    {z | z ∈ L₁ ∧ z ∈ L₂} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_and (test_of_mem_P h₁) (test_of_mem_P h₂))
  convert h using 1
  ext z
  by_cases a : z ∈ L₁ <;> by_cases b : z ∈ L₂ <;> simp [MultiTapeTM.indicator, a, b]

/-- **`P` is closed under union** (branching on the first test). -/
theorem union_mem_P {L₁ L₂ : Language Bool} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    {z | z ∈ L₁ ∨ z ∈ L₂} ∈ P := by
  have ht : PolyTimeComputable
      (fun z => [MultiTapeTM.indicator L₁ z || MultiTapeTM.indicator L₂ z]) := by
    convert polyTimeComputable_ite (test_of_mem_P h₁) (polyTimeComputable_const [true])
      (test_of_mem_P h₂) using 1
    funext z
    cases MultiTapeTM.indicator L₁ z <;> rfl
  convert mem_P_of_test ht using 1
  ext z
  by_cases a : z ∈ L₁ <;> by_cases b : z ∈ L₂ <;> simp [MultiTapeTM.indicator, a, b]

/-- The empty language is in `P`. -/
theorem empty_mem_P : ({_z | false = true} : Language Bool) ∈ P :=
  mem_P_of_test (polyTimeComputable_const [false])

/-- The full language is in `P`. -/
theorem univ_mem_P : ({_z | true = true} : Language Bool) ∈ P :=
  mem_P_of_test (polyTimeComputable_const [true])

/-- **`P` is closed under Boolean functions of finitely many tests**: if each test
`b i` decides a language in `P`, so does `z ↦ F (b · z)` for any `F`.

**Proof sketch.** The language is the finite union, over the valuations `β` with
`F β = true`, of the finite intersections `⋂ᵢ {z | b i z = β i}`; each set in the
intersection is a test language or its complement. -/
theorem mem_P_of_atoms {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → List Bool → Bool)
    (hb : ∀ i, ({z | b i z = true} : Language Bool) ∈ P) (F : (ι → Bool) → Bool) :
    ({z | F (fun i => b i z) = true} : Language Bool) ∈ P := by
  classical
  -- one valuation
  have hval : ∀ β : ι → Bool, ∀ s : Finset ι,
      ({z | ∀ i ∈ s, b i z = β i} : Language Bool) ∈ P := by
    intro β s
    induction s using Finset.induction_on with
    | empty => simpa using univ_mem_P
    | insert i s hi ih =>
      have hi' : ({z | b i z = β i} : Language Bool) ∈ P := by
        cases hβ : β i
        · have := compl_mem_P (hb i)
          convert this using 1
          ext z
          change b i z = false ↔ ¬ (b i z = true)
          simp
        · exact hb i
      have := inter_mem_P hi' ih
      convert this using 1
      ext z
      simp
  have hunion : ∀ s : Finset (ι → Bool),
      ({z | ∃ β ∈ s, ∀ i, b i z = β i} : Language Bool) ∈ P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using empty_mem_P
    | insert β s hβ ih =>
      have h1 := hval β Finset.univ
      have := union_mem_P h1 ih
      convert this using 1
      ext z
      change (∃ β' ∈ insert β s, ∀ i, b i z = β' i) ↔
        (∀ i ∈ Finset.univ, b i z = β i) ∨ (∃ β' ∈ s, ∀ i, b i z = β' i)
      simp
  have h := hunion (Finset.univ.filter fun β => F β = true)
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz; exact ⟨_, hz, fun i => rfl⟩
  · rintro ⟨β, hβ, hb'⟩
    have : (fun i => b i z) = β := funext hb'
    rw [this]; exact hβ

/-! ### Length comparisons -/

/-- The words whose two components under the total default projections
(`pairFstD`/`pairSndD`, both `[]` on malformed input) have equal length form a language
in `P`. Malformed words project to `([], [])` and are therefore members — e.g. `[]`
itself; the well-formed-pair corollaries below are unaffected (P0 round 1, finding 5). -/
theorem lenEq_mem_P : {z : List Bool | (pairFstD z).length = (pairSndD z).length} ∈ P := by
  have h := mem_P_of_test polyTimeComputable_lenEq
  simpa using h

/-- The words whose second default-projected component is at most as long as the first
form a language in `P` — with the same totalization as `Complexity.lenEq_mem_P`:
malformed words project to `([], [])` and are members. -/
theorem lenLe_mem_P : {z : List Bool | (pairSndD z).length ≤ (pairFstD z).length} ∈ P := by
  have h := mem_P_of_test polyTimeComputable_lenLe
  simpa using h

/-- Comparing the lengths of two polynomial-time computable strings is in `P`. -/
theorem lenEq_preimage_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : {z | (f z).length = (g z).length} ∈ P := by
  have h := preimage_mem_P lenEq_mem_P (hf.pairEncode hg)
  simpa using h

/-- `|g z| ≤ |f z|` for polynomial-time `f`, `g` is decidable in `P`. -/
theorem lenLe_preimage_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : {z | (g z).length ≤ (f z).length} ∈ P := by
  have h := preimage_mem_P lenLe_mem_P (hf.pairEncode hg)
  simpa using h

end Complexity
