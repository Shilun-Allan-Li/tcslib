/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.SpaceComplexity.Logspace.QueryReshape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logspace reductions and `NL`-completeness

[AB09, §4.3, Definition 4.16 and Lemma 4.17]: reductions computed in
logarithmic space — rendered, as the book does, through *implicitly* logspace
computable functions (`Complexity.ImplicitlyLogspaceComputable`, the received
P0 surface), since a logspace machine cannot store its output. Phase P4.4 of
`AroraBarakChapters3-4Plan.md`; the composition theorem stated here is
exactly the general Lemma 4.17 that the P0 reception round recorded as *not*
delivered (its note 10) — the received `UnaryLogspace.counterProg` closure
remains the special case.

## Main definitions

* `Complexity.LogspaceReducible` (`≤ₗ`) — [AB09, Definition 4.16].
* `Complexity.NLComplete` — `NL`-membership plus `NL`-hardness under `≤ₗ`.
  [AB09, Definition 4.16]

## Main results (phase-P4.4 statements proved)

* `Complexity.ImplicitlyLogspaceComputable.comp` — the composition engine
  ([AB09, Lemma 4.17's proof], Figure 4.3's virtual input tape).
* `Complexity.LogspaceReducible.trans` — [AB09, Lemma 4.17(1)].
* `Complexity.mem_LOGSPACE_of_logspaceReducible` — [AB09, Lemma 4.17(2)].
* `Complexity.LogspaceReducible.polyTimeReducible` — `≤ₗ` refines `≤ₚ`.
* `Complexity.NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` — an `NL`-complete
  language in `L` collapses `NL` to `L`. [AB09, after Lemma 4.17]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Definition 4.16, Lemma 4.17,
  Figure 4.3.)
-/

namespace Complexity

open Turing

/-- **Logspace reducibility** [AB09, Definition 4.16]: `B ≤ₗ C` when some
implicitly logspace computable `f` satisfies `x ∈ B ↔ f x ∈ C` for every
string — the reduction is never written down whole, only queried bit by bit
(`Complexity.ImplicitlyLogspaceComputable`, with its received divergences:
`0`-based indices and the campaign polynomial normal form). -/
def LogspaceReducible (B C : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool, ImplicitlyLogspaceComputable f ∧
    ∀ x, x ∈ B ↔ f x ∈ C

@[inherit_doc] scoped infix:50 " ≤ₗ " => LogspaceReducible

/-- **`NL`-completeness** [AB09, Definition 4.16]: membership in `NL`
together with `NL`-hardness under logspace reductions. (Polynomial-time
reductions would trivialize this notion — `Complexity.polyTimeReducible_of_mem_NL`,
Exercise 4.3, phase P4.2.) -/
def NLComplete (C : Language Bool) : Prop :=
  C ∈ NL ∧ ∀ B ∈ NL, B ≤ₗ C

/-- The composite output bound of [AB09, Lemma 4.17] (P4.4 audit, question 2).

**Proof sketch.** Absorb the added one into `C + 1`, apply the second polynomial
bound monotonically, and distribute powers. This is the pre-ship D2 bound. -/
private theorem comp_length_le {f g : List Bool → List Bool} {C c D d : ℕ}
    (hf : ∀ x, (f x).length ≤ C * (x.length + 1) ^ c)
    (hg : ∀ y, (g y).length ≤ D * (y.length + 1) ^ d) (x : List Bool) :
    (g (f x)).length ≤ D * (C + 1) ^ d * (x.length + 1) ^ (c * d) := by
  have h1 : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  have h2 : (f x).length + 1 ≤ (C + 1) * (x.length + 1) ^ c := by
    have := hf x
    have e : (C + 1) * (x.length + 1) ^ c = C * (x.length + 1) ^ c + (x.length + 1) ^ c := by
      ring
    omega
  calc (g (f x)).length ≤ D * ((f x).length + 1) ^ d := hg _
    _ ≤ D * ((C + 1) * (x.length + 1) ^ c) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 d)
    _ = D * (C + 1) ^ d * (x.length + 1) ^ (c * d) := by rw [mul_pow, ← pow_mul]; ring

/-- **Composition of implicitly logspace computable functions** ([AB09,
Lemma 4.17's proof]; proved — phase P4.4, **the general
composition the P0 round recorded as undelivered**): if `f` and `g` are
implicitly logspace computable, so is `g ∘ f`.

**Proof sketch.** [AB09, Figure 4.3]: to answer a bit or length query about
`g (f x)`, run `g`'s query machine against a **virtual input tape** holding
`f x` — maintain the index of the cell `g`'s head would scan (logarithmic in
`|f x|`, hence in `|x|` by `f`'s polynomial output bound), and whenever
`g`'s machine reads, suspend it and answer with `f`'s bit/length queries on
`⟨x, i⟩`. The received `LogProg` call protocol does not host this shape by
itself: a call's virtual input is read physically (the whole input, or its
leading run of `1`s, followed by register words), so no call can serve `g`'s
input from `f`'s queries (P0 reception audit, note 10). Fill route (phase
P4.4b, `audits/ch4-p44-resolutions-addendum.md`): both query languages of
`g ∘ f` are preimages of `g`'s along `Complexity.compQ f`
(`Complexity.mem_indexLang_compQ_iff`), hence in `L` by
`Complexity.mem_LOGSPACE_preimage` (the Fig. 4.3 engine,
`Complexity.LogProg.OIS`) and `Complexity.ImplicitlyLogspaceComputable.compQ`.
Obligations, named: the polynomial bound of the composite (`f`'s and `g`'s
bounds composed, `D (C + 1)^d (|x| + 1)^{cd}`); the two preimage memberships;
the index bookkeeping, which lives in `compQ`'s machines. (Sketch prose
corrected at phase P4.4b; the statement is unchanged.) -/
theorem ImplicitlyLogspaceComputable.comp {f g : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) (hg : ImplicitlyLogspaceComputable g) :
    ImplicitlyLogspaceComputable (g ∘ f) := by
  have hQ := hf.compQ
  obtain ⟨⟨C, c, hC⟩, -, -⟩ := hf
  obtain ⟨⟨D, d, hD⟩, hgb, hgl⟩ := hg
  refine ⟨⟨D * (C + 1) ^ d, c * d, comp_length_le (f := f) (g := g) hC hD⟩, ?_, ?_⟩
  · rw [show indexLang (fun x i => ((g ∘ f) x).getD i false = true) =
        ({w | Complexity.compQ f w ∈ indexLang fun y i => (g y).getD i false = true} : Language Bool) from
      Set.ext (mem_indexLang_compQ_iff f fun y i => (g y).getD i false = true)]
    exact mem_LOGSPACE_preimage hQ hgb
  · rw [show indexLang (fun x i => i < ((g ∘ f) x).length) =
        ({w | Complexity.compQ f w ∈ indexLang fun y i => i < (g y).length} : Language Bool) from
      Set.ext (mem_indexLang_compQ_iff f fun y i => i < (g y).length)]
    exact mem_LOGSPACE_preimage hQ hgl

/-- **Logspace reducibility is transitive** ([AB09, Lemma 4.17(1)]; proved).

**Proof sketch.** `Complexity.ImplicitlyLogspaceComputable.comp` on the two
reduction functions; the membership equivalences chain. -/
theorem LogspaceReducible.trans {B C D : Language Bool} (h₁ : B ≤ₗ C)
    (h₂ : C ≤ₗ D) : B ≤ₗ D := by
  obtain ⟨f, hf, hB⟩ := h₁
  obtain ⟨g, hg, hC⟩ := h₂
  exact ⟨g ∘ f, hf.comp hg, fun x => (hB x).trans (hC (f x))⟩

/-- **Logspace reductions preserve `L` downward** ([AB09, Lemma 4.17(2)];
proved): if `B ≤ₗ C` and `C ∈ LOGSPACE` then `B ∈ LOGSPACE`.

**Proof sketch.** Directly by the preimage theorem (route change 1 of
`audits/ch4-p44-resolutions-addendum.md`). Unpack `h` as an implicitly
logspace computable `f` with `x ∈ B ↔ f x ∈ C`. Then `B = {x | f x ∈ C}` by
`Set.ext`, and `Complexity.mem_LOGSPACE_preimage hf hC` concludes. The
preimage engine, the oracle-input simulator `Complexity.LogProg.OIS` ([AB09,
Fig. 4.3]'s construction), cites nothing from this file, so there is no
circularity (round-1 audit, finding 2). The earlier route through `C`'s
characteristic function and `comp` is superseded: deciding `χ_C`'s bit
language needs the engine itself. (Sketch prose corrected at the P4.4b
statement gate; the statement is unchanged.) -/
theorem mem_LOGSPACE_of_logspaceReducible {B C : Language Bool} (h : B ≤ₗ C)
    (hC : C ∈ LOGSPACE) : B ∈ LOGSPACE := by
  obtain ⟨f, hf, hB⟩ := h
  rw [show B = ({x | f x ∈ C} : Language Bool) from Set.ext hB]
  exact mem_LOGSPACE_preimage hf hC

/-- **`≤ₗ` refines `≤ₚ`**: a logspace reduction is in
particular a polynomial-time reduction.

**Proof sketch.** The received
`Complexity.ImplicitlyLogspaceComputable.polyTimeComputable` turns the
implicit witness into a whole-output polynomial-time machine; the
equivalences carry over verbatim. -/
theorem LogspaceReducible.polyTimeReducible {B C : Language Bool}
    (h : B ≤ₗ C) : B ≤ₚ C := by
  obtain ⟨f, hf, hB⟩ := h
  exact ⟨f, hf.polyTimeComputable, hB⟩

/-- **An `NL`-complete language in `L` collapses `NL`** ([AB09, the remark
after Lemma 4.17]; proved): if `C` is `NL`-complete and
`C ∈ LOGSPACE`, then `NL = LOGSPACE`.

**Proof sketch.** `⊇` is `Complexity.LOGSPACE_subset_NL` (phase P4.1). `⊆`:
a member of `NL` reduces to `C` (completeness) and
`Complexity.mem_LOGSPACE_of_logspaceReducible` pulls membership back along
the reduction. -/
theorem NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE {C : Language Bool}
    (h : NLComplete C) (hC : C ∈ LOGSPACE) : NL = LOGSPACE := by
  exact Set.Subset.antisymm
    (fun B hB => mem_LOGSPACE_of_logspaceReducible (h.2 B hB) hC) LOGSPACE_subset_NL

end Complexity
