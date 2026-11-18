/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringGraph
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Bridge

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
attribute [local irreducible] SATtoColor.EdgeRelation SATtoColor.Is3Colorable SATtoColor.IsSatisfiable SATtoColor.ReductionGraph SATtoColor.SatisfiesClause SATtoColor.SatisfiesLiteral SATtoColor.SatisfiesSat3 TCSlib.Cryptography.LevinHardness.clauseEquiv TCSlib.Cryptography.LevinHardness.clauseLit TCSlib.Cryptography.LevinHardness.clauseSat TCSlib.Cryptography.LevinHardness.gadgetAdj TCSlib.Cryptography.LevinHardness.gadgetEdge TCSlib.Cryptography.LevinHardness.gadgetN TCSlib.Cryptography.LevinHardness.gadgetSimpleGraph TCSlib.Cryptography.LevinHardness.litEquiv TCSlib.Cryptography.LevinHardness.litVal TCSlib.Cryptography.LevinHardness.vertexEquiv

/-!
# Soundness of the gadget graph through the course reduction

The gadget graph of `Gadget.lean` maps the course reduction's graph `SATtoColor.ReductionGraph f`
(`Complexity/NPReductions/ThreeSATToColoring.lean`, course material) homomorphically into itself
along the vertex equivalence `vertexEquiv K`, for the formula `f` of the clause codes accepted by
`mem`. A 3-colouring of the gadget graph therefore pulls back to a 3-colouring of
`ReductionGraph f`, which by the course theorem `SATtoColor.SATtoColorReduction` makes `f`
satisfiable: the soundness of the reduction is **not** re-proved here, it is transported.
The definitions of the course file are read only through the quarantined readers of
`LevinHardness/Bridge.lean` (user ruling, disclosed there).

**Statement change (disclosed).** The brief proposes an explicit graph isomorphism; soundness
needs only the homomorphism `ReductionGraph f →g gadgetSimpleGraph K mem` (the other direction,
completeness, is the explicit colouring of `ColoringWitness.lean`), so only that is stated.

## Main definitions

* `TCSlib.Cryptography.LevinHardness.gadgetFormula` — the course formula of the codes in `mem`.
* `TCSlib.Cryptography.LevinHardness.reductionGraphHom` — the homomorphism.

## Main results

* `TCSlib.Cryptography.LevinHardness.gadgetEdge_or_of_edgeRelation` — edges are preserved.
* `TCSlib.Cryptography.LevinHardness.isSatisfiable_of_colorable` — soundness through
  `SATtoColorReduction`.
* `TCSlib.Cryptography.LevinHardness.exists_clauseSat_of_colorable` — a 3-colourable gadget
  graph has an assignment, `false` beyond the `K` variables, satisfying every clause code accepted
  by `mem`.

## References

* CS 294-268 course material (UC Berkeley, Spring 2026, V. Guruswami), the 3SAT → 3-colouring
  reduction of `Complexity/NPReductions/ThreeSATToColoring.lean`.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.3.)
-/

namespace TCSlib.Cryptography.LevinHardness

open SATtoColor

/-- **Every edge of the course reduction is an edge of the gadget graph** along the vertex
equivalence: if `f` contains only clauses whose codes pass `mem`, then
`EdgeRelation f a b` implies that `gadgetEdge K mem` joins `(vertexEquiv K).symm a` and
`(vertexEquiv K).symm b` in one of the two orientations.

**Proof sketch.** Case analysis over the nine pairs of vertex kinds, reading `EdgeRelation`
through the bridge readers and the vertex numbers through `vertexEquiv_symm_*`: palette pairs,
base–literal, a literal and its negation, gadget node `5` with the base or the false node, a
literal with gadget node `0`, `1` or `4` of a clause containing it (`clauseLit_clauseEquiv_symm`),
and the fourteen ordered gadget pairs of a clause of `f` (`mem` holds by hypothesis); in each case
the corresponding disjunct of `gadgetEdge_eq` holds by arithmetic on the vertex numbers. -/
theorem gadgetEdge_or_of_edgeRelation (K : ℕ) (mem : ℕ → Bool) (f : Sat3 (Fin K))
    (hf : ∀ c : SATtoColor.Clause (Fin K), c ∈ f → mem ((clauseEquiv K).symm c) = true)
    (a b : OutputVertex (Fin K)) (h : EdgeRelation f a b) :
    (gadgetEdge K mem ((vertexEquiv K).symm a) ((vertexEquiv K).symm b) ||
      gadgetEdge K mem ((vertexEquiv K).symm b) ((vertexEquiv K).symm a)) = true := by
  have hA := ((vertexEquiv K).symm a).isLt
  have hB := ((vertexEquiv K).symm b).isLt
  rw [Bool.or_eq_true, gadgetEdge_eq, gadgetEdge_eq]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases a with p | l | ⟨c, i⟩ <;> rcases b with p' | l' | ⟨c', j⟩
  · rw [Bridge.edgeRelation_palette_palette] at h
    rw [vertexEquiv_symm_palette, vertexEquiv_symm_palette] at *
    left; left; left; left; left; left; exact ⟨p.isLt, p'.isLt⟩
  · rw [Bridge.edgeRelation_palette_literal] at h
    subst h
    rw [vertexEquiv_symm_palette, vertexEquiv_symm_literalNode] at *
    have := ((litEquiv K).symm l').isLt
    left; left; left; left; left; right; refine ⟨⟨rfl, by omega⟩, by omega⟩
  · rw [Bridge.edgeRelation_palette_gadget] at h
    obtain ⟨rfl, hp⟩ := h
    rw [vertexEquiv_symm_palette, vertexEquiv_symm_clauseGadget] at *
    right; right
    refine ⟨⟨⟨by omega, hB⟩, by simp; omega⟩, by rcases hp with rfl | rfl <;> simp⟩
  · rw [Bridge.edgeRelation_literal_palette] at h
    subst h
    rw [vertexEquiv_symm_palette, vertexEquiv_symm_literalNode] at *
    have := ((litEquiv K).symm l).isLt
    right; left; left; left; left; right; refine ⟨⟨rfl, by omega⟩, by omega⟩
  · rw [Bridge.edgeRelation_literal_literal] at h
    obtain ⟨x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
    · rw [vertexEquiv_symm_literalNode, vertexEquiv_symm_literalNode, litEquiv_symm_pos,
        litEquiv_symm_neg] at *
      have := x.isLt
      left; left; left; left; right
      refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
    · rw [vertexEquiv_symm_literalNode, vertexEquiv_symm_literalNode, litEquiv_symm_pos,
        litEquiv_symm_neg] at *
      have := x.isLt
      right; left; left; left; right
      refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩
  · rw [Bridge.edgeRelation_literal_gadget] at h
    rw [vertexEquiv_symm_literalNode, vertexEquiv_symm_clauseGadget] at *
    have hl := ((litEquiv K).symm l).isLt
    have hj := j.isLt
    have e : (3 + 2 * K + 6 * ((clauseEquiv K).symm c' : ℕ) + (j : ℕ) - (3 + 2 * K)) / 6 =
        ((clauseEquiv K).symm c' : ℕ) := by omega
    have e' : (3 + 2 * K + 6 * ((clauseEquiv K).symm c' : ℕ) + (j : ℕ) - (3 + 2 * K)) % 6 =
        (j : ℕ) := by omega
    rw [e, e', clauseLit_clauseEquiv_symm, clauseLit_clauseEquiv_symm,
      clauseLit_clauseEquiv_symm]
    left; left; right
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, hB⟩, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; left; exact ⟨by simp, rfl⟩
    · left; right; exact ⟨by simp, rfl⟩
    · right; exact ⟨by simp, rfl⟩
  · rw [Bridge.edgeRelation_gadget_palette] at h
    obtain ⟨rfl, hp⟩ := h
    rw [vertexEquiv_symm_palette, vertexEquiv_symm_clauseGadget] at *
    left; right
    refine ⟨⟨⟨by omega, hA⟩, by simp; omega⟩, by rcases hp with rfl | rfl <;> simp⟩
  · rw [Bridge.edgeRelation_gadget_literal] at h
    rw [vertexEquiv_symm_literalNode, vertexEquiv_symm_clauseGadget] at *
    have hl := ((litEquiv K).symm l').isLt
    have hi := i.isLt
    have e : (3 + 2 * K + 6 * ((clauseEquiv K).symm c : ℕ) + (i : ℕ) - (3 + 2 * K)) / 6 =
        ((clauseEquiv K).symm c : ℕ) := by omega
    have e' : (3 + 2 * K + 6 * ((clauseEquiv K).symm c : ℕ) + (i : ℕ) - (3 + 2 * K)) % 6 =
        (i : ℕ) := by omega
    rw [e, e', clauseLit_clauseEquiv_symm, clauseLit_clauseEquiv_symm,
      clauseLit_clauseEquiv_symm]
    right; left; right
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, hA⟩, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; left; exact ⟨by simp, rfl⟩
    · left; right; exact ⟨by simp, rfl⟩
    · right; exact ⟨by simp, rfl⟩
  · rw [Bridge.edgeRelation_gadget_gadget] at h
    obtain ⟨rfl, hc, hij⟩ := h
    rw [vertexEquiv_symm_clauseGadget, vertexEquiv_symm_clauseGadget] at *
    have hi := i.isLt
    have hj := j.isLt
    have hm := hf c hc
    have e1 : (3 + 2 * K + 6 * ((clauseEquiv K).symm c : ℕ) + (i : ℕ) - (3 + 2 * K)) / 6 =
        ((clauseEquiv K).symm c : ℕ) := by omega
    have e2 : (3 + 2 * K + 6 * ((clauseEquiv K).symm c : ℕ) + (i : ℕ) - (3 + 2 * K)) % 6 =
        (i : ℕ) := by omega
    have e3 : (3 + 2 * K + 6 * ((clauseEquiv K).symm c : ℕ) + (j : ℕ) - (3 + 2 * K)) / 6 =
        ((clauseEquiv K).symm c : ℕ) := by omega
    have e4 : (3 + 2 * K + 6 * ((clauseEquiv K).symm c : ℕ) + (j : ℕ) - (3 + 2 * K)) % 6 =
        (j : ℕ) := by omega
    rw [e1, e2, e3, e4]
    have hb : ∀ x : ℕ, 3 + 2 * K ≤ 3 + 2 * K + 6 * ((clauseEquiv K).symm c : ℕ) + x :=
      fun x => by omega
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first
      | (left; left; left; right
         exact ⟨⟨⟨⟨⟨⟨hb _, hA⟩, hb _⟩, hB⟩, rfl⟩, hm⟩, by decide⟩)
      | (right; left; left; right
         exact ⟨⟨⟨⟨⟨⟨hb _, hB⟩, hb _⟩, hA⟩, rfl⟩, hm⟩, by decide⟩)

/-- **The course formula of a code test**: the clauses `clauseEquiv K c` of the codes
`c < (2K)³` with `mem c`, `gadgetFormula K mem = ((finRange (2K)³).filter mem).map (clauseEquiv K)`.
-/
def gadgetFormula (K : ℕ) (mem : ℕ → Bool) : Sat3 (Fin K) :=
  ((List.finRange ((2 * K) ^ 3)).filter fun c => mem c.val).map (clauseEquiv K)

/-- The defining equation of `gadgetFormula`. -/
theorem gadgetFormula_eq (K : ℕ) (mem : ℕ → Bool) :
    gadgetFormula K mem = ((List.finRange ((2 * K) ^ 3)).filter fun c => mem c.val).map
      (clauseEquiv K) := rfl

/-- Every clause of `gadgetFormula K mem` has a code accepted by `mem`:
`c ∈ gadgetFormula K mem → mem ((clauseEquiv K).symm c) = true`. -/
theorem mem_of_mem_gadgetFormula {K : ℕ} {mem : ℕ → Bool} {c : SATtoColor.Clause (Fin K)}
    (hc : c ∈ gadgetFormula K mem) : mem ((clauseEquiv K).symm c) = true := by
  rw [gadgetFormula_eq, List.mem_map] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  rw [Equiv.symm_apply_apply]
  exact (List.mem_filter.1 hx).2

/-- **The homomorphism from the course graph into the gadget graph**:
`ReductionGraph (gadgetFormula K mem) →g gadgetSimpleGraph K mem`, the map `(vertexEquiv K).symm`
(`gadgetEdge_or_of_edgeRelation`, distinct vertices having distinct numbers). -/
def reductionGraphHom (K : ℕ) (mem : ℕ → Bool) :
    ReductionGraph (gadgetFormula K mem) →g gadgetSimpleGraph K mem where
  toFun := (vertexEquiv K).symm
  map_rel' {a b} h := by
    obtain ⟨hne, hab⟩ := (Bridge.reductionGraph_adj _ a b).1 h
    rw [gadgetSimpleGraph_adj, gadgetAdj_eq, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨fun he => hne ((vertexEquiv K).symm.injective (Fin.ext he)), ?_⟩
    rcases hab with hab | hab
    · exact gadgetEdge_or_of_edgeRelation K mem _ (fun c => mem_of_mem_gadgetFormula) a b hab
    · rw [Bool.or_comm]
      exact gadgetEdge_or_of_edgeRelation K mem _ (fun c => mem_of_mem_gadgetFormula) b a hab

/-- The underlying map of `reductionGraphHom` is `(vertexEquiv K).symm`. -/
theorem reductionGraphHom_apply (K : ℕ) (mem : ℕ → Bool) (a : OutputVertex (Fin K)) :
    reductionGraphHom K mem a = (vertexEquiv K).symm a := rfl

/-- **Soundness, transported from the course theorem**: if the gadget graph is 3-colourable then
the course formula of its codes is satisfiable,
`(gadgetSimpleGraph K mem).Colorable 3 → IsSatisfiable (gadgetFormula K mem)`
(`SATtoColor.SATtoColorReduction` after pulling the colouring back along
`reductionGraphHom`). -/
theorem isSatisfiable_of_colorable {K : ℕ} {mem : ℕ → Bool}
    (h : (gadgetSimpleGraph K mem).Colorable 3) : IsSatisfiable (gadgetFormula K mem) := by
  obtain ⟨C⟩ := h
  exact (SATtoColorReduction _).2 ((Bridge.is3Colorable_iff _).2
    ⟨C.comp (reductionGraphHom K mem)⟩)

/-- Glue: the course truth value of a literal of code `ℓ` is `litVal` of the code, for the
assignment `val v = a v` on `v < K` (`false` beyond):
`SatisfiesLiteral a (litEquiv K ℓ) = litVal val ℓ`. -/
theorem satisfiesLiteral_litEquiv {K : ℕ} (a : Fin K → Bool) (ℓ : Fin (2 * K)) :
    SatisfiesLiteral a (litEquiv K ℓ) =
      litVal (fun v => if h : v < K then a ⟨v, h⟩ else false) ℓ := by
  have hl := ℓ.isLt
  have hK : (ℓ : ℕ) / 2 < K := by omega
  rw [litEquiv_apply, litVal_eq]
  by_cases h : (ℓ : ℕ) % 2 = 0
  · rw [if_pos h, if_pos h, Bridge.satisfiesLiteral_pos, dif_pos hK]
  · rw [if_neg h, if_neg h, Bridge.satisfiesLiteral_neg, dif_pos hK]

/-- **A 3-colourable gadget graph has a satisfying assignment of its clause codes**: there is
`val : ℕ → Bool`, `false` on `v ≥ K`, with `clauseSat K val c = true` for every code `c < (2K)³`
with `mem c = true`.

**Proof sketch.** By `isSatisfiable_of_colorable` some `a : Fin K → Bool` satisfies every clause
of `gadgetFormula K mem`; for a code `c` with `mem c`, the clause `clauseEquiv K c` is in the
formula, its three literals are `litEquiv K` of the codes `clauseLit K c j`
(`clauseEquiv_apply`), and their course values are `litVal val` of those codes
(`satisfiesLiteral_litEquiv`), which is `clauseSat K val c` (`clauseSat_eq`). -/
theorem exists_clauseSat_of_colorable {K : ℕ} {mem : ℕ → Bool}
    (h : (gadgetSimpleGraph K mem).Colorable 3) :
    ∃ val : ℕ → Bool, (∀ v, K ≤ v → val v = false) ∧
      ∀ c, c < (2 * K) ^ 3 → mem c = true → clauseSat K val c = true := by
  obtain ⟨a, ha⟩ := (Bridge.isSatisfiable_iff _).1 (isSatisfiable_of_colorable h)
  refine ⟨fun v => if h : v < K then a ⟨v, h⟩ else false,
    fun v hv => dif_neg (Nat.not_lt.2 hv), fun c hc hm => ?_⟩
  rw [Bridge.satisfiesSat3_eq, List.all_eq_true] at ha
  have hmem : clauseEquiv K ⟨c, hc⟩ ∈ gadgetFormula K mem := by
    rw [gadgetFormula_eq]
    exact List.mem_map_of_mem (List.mem_filter.2 ⟨List.mem_finRange _, hm⟩)
  have hs := ha _ hmem
  rw [Bridge.satisfiesClause_eq, clauseEquiv_apply, satisfiesLiteral_litEquiv,
    satisfiesLiteral_litEquiv, satisfiesLiteral_litEquiv] at hs
  rw [clauseSat_eq]
  exact hs

end TCSlib.Cryptography.LevinHardness
