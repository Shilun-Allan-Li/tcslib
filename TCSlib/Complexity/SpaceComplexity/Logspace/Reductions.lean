/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly
import TCSlib.Complexity.ClassNP.Reductions

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

## Main results (all sorried; phase-P4.4 statements)

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

/-- **Composition of implicitly logspace computable functions** ([AB09,
Lemma 4.17's proof]; spec, fill pending — phase P4.4, **the general
composition the P0 round recorded as undelivered**): if `f` and `g` are
implicitly logspace computable, so is `g ∘ f`.

**Proof sketch.** [AB09, Figure 4.3]: to answer a bit or length query about
`g (f x)`, run `g`'s query machine against a **virtual input tape** holding
`f x` — maintain the index of the cell `g`'s head would scan (logarithmic in
`|f x|`, hence in `|x|` by `f`'s polynomial output bound), and whenever
`g`'s machine reads, suspend it and answer with `f`'s bit/length queries on
`⟨x, i⟩`. The received `LogProg` layer is built for exactly this shape: the
virtual-input discipline is `Machines/Layout`, the suspended-call protocol
is `Machines/{Program,Sim,Call,CallReturn,Compile}` (`compile_correct`/
`compile_space`), and the decider assembly is `arm_decides` — the fill
instantiates them rather than building machines by hand. Obligations, named:
the polynomial bound of the composite (`f`'s and `g`'s bounds composed); the
two `indexLang` memberships of `g ∘ f` via the call protocol; the index
bookkeeping (binary counters within `logSpace`, the `Machines/Bin` layer). -/
theorem ImplicitlyLogspaceComputable.comp {f g : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) (hg : ImplicitlyLogspaceComputable g) :
    ImplicitlyLogspaceComputable (g ∘ f) := by
  sorry

/-- **Logspace reducibility is transitive** ([AB09, Lemma 4.17(1)]; spec,
fill pending).

**Proof sketch.** `Complexity.ImplicitlyLogspaceComputable.comp` on the two
reduction functions; the membership equivalences chain. -/
theorem LogspaceReducible.trans {B C D : Language Bool} (h₁ : B ≤ₗ C)
    (h₂ : C ≤ₗ D) : B ≤ₗ D := by
  sorry

/-- **Logspace reductions preserve `L` downward** ([AB09, Lemma 4.17(2)];
spec, fill pending): if `B ≤ₗ C` and `C ∈ LOGSPACE` then `B ∈ LOGSPACE`.

**Proof sketch.** [AB09]'s own route: `C`'s characteristic function is
implicitly logspace computable (its bit language holds at a genuine pair
`⟨x, i⟩` iff `i = 0 ∧ x ∈ C`; its length language is **exactly**
`{pairEncode x [] | x}` — a regular language, not a total one: index `1` and
every malformed string are rejected; round-1 audit, finding 1), so the
composition `χ_C ∘ f` is implicitly logspace computable by
`Complexity.ImplicitlyLogspaceComputable.comp`, and deciding `B` is its bit
query at index `0` — a `LOGSPACE` membership by a fixed-index
**paired-input** specialization (named fill obligation): the index-`0` query
string is `pairEncode x [] = dbl x ++ [false, true]`, the *doubled* word with
its separator, not `x` itself, so the specialization simulates the query
decider on that doubled virtual input directly — independent of this very
theorem, avoiding circularity (round-1 audit, finding 2). -/
theorem mem_LOGSPACE_of_logspaceReducible {B C : Language Bool} (h : B ≤ₗ C)
    (hC : C ∈ LOGSPACE) : B ∈ LOGSPACE := by
  sorry

/-- **`≤ₗ` refines `≤ₚ`** (spec, fill pending): a logspace reduction is in
particular a polynomial-time reduction.

**Proof sketch.** The received
`Complexity.ImplicitlyLogspaceComputable.polyTimeComputable` turns the
implicit witness into a whole-output polynomial-time machine; the
equivalences carry over verbatim. -/
theorem LogspaceReducible.polyTimeReducible {B C : Language Bool}
    (h : B ≤ₗ C) : B ≤ₚ C := by
  sorry

/-- **An `NL`-complete language in `L` collapses `NL`** ([AB09, the remark
after Lemma 4.17]; spec, fill pending): if `C` is `NL`-complete and
`C ∈ LOGSPACE`, then `NL = LOGSPACE`.

**Proof sketch.** `⊇` is `Complexity.LOGSPACE_subset_NL` (phase P4.1). `⊆`:
a member of `NL` reduces to `C` (completeness) and
`Complexity.mem_LOGSPACE_of_logspaceReducible` pulls membership back along
the reduction. -/
theorem NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE {C : Language Bool}
    (h : NLComplete C) (hC : C ∈ LOGSPACE) : NL = LOGSPACE := by
  sorry

end Complexity
