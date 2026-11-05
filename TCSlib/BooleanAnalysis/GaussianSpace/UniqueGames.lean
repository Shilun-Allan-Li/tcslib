/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.GaussianSpace.UniqueGamesDefinitions
import TCSlib.BooleanAnalysis.GaussianSpace.MajorityIsStablest

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Unique-Games hardness of Max-Cut: statement layer

## Main definitions

Concrete encodings, objectives, promise reductions and the Unique Games
Conjecture are in `UniqueGamesDefinitions`.

## Main results

Codec/graph transport, the bridge to existing NP-hardness, and Theorem 11.74.
All new proofs remain placeholders. This is a conditional computational
statement, not an unproved axiom asserting the Unique Games Conjecture itself.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §7.3, Theorem 7.40, Exercises 7.27, 7.30(h), 7.31,
  §11.7, Theorem 11.74 and Exercise 11.36.
* [KKMO07] S. Khot, G. Kindler, E. Mossel and R. O'Donnell, Optimal inapproximability
  results for MAX-CUT and other 2-variable CSPs?, SIAM Journal on Computing 37
  (2007), 319–357 (conference version 2004).
-/

open scoped BigOperators

namespace BooleanAnalysis.GaussianSpace.UniqueGames

/-- Natural-number rows round-trip through the existing binary CNF codec.
This is a representation adapter for [OD14, §11.7]'s finite CSP inputs.
**Proof sketch.** Apply the existing CNF round-trip theorem and remove the
constant true polarities from each decoded row. -/
theorem parseNatRows_encodeNatRows (rows : List (List ℕ)) :
    parseNatRows (encodeNatRows rows) = some rows := sorry

/-- A valid Unique Games constraint list round-trips through its encoding.
[OD14, §7.3, Unique Games]
**Proof sketch.** Use the row round trip and validate each permutation table. -/
theorem parseUniqueGame_encodeUniqueGame (q : ℕ) (G : List UniqueGameConstraint)
    (hG : ∀ e ∈ G, e.Valid q) :
    parseUniqueGame q (encodeUniqueGame G) = some G := sorry

/-- A loop-free edge list round-trips through the Max-Cut encoding.
[OD14, §11.7, Max-Cut]
**Proof sketch.** Use the row round trip and the endpoint inequality of each edge. -/
theorem parseMaxCut_encodeMaxCut (E : List (ℕ × ℕ))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) : parseMaxCut (encodeMaxCut E) = some E := sorry

/-- Every nonempty loop-free edge list gives a valid normalized weighted graph.
[OD14, §11.7, random-edge convention]
**Proof sketch.** Endpoint bounds come from the existing CNF variable-count
formula. Symmetrized counts are nonnegative, have zero diagonal and sum to one. -/
theorem maxCutGraph_valid (E : List (ℕ × ℕ)) (hne : E ≠ [])
    (hE : ∀ e ∈ E, e.1 ≠ e.2) : MaxCut.IsValid (maxCutGraph E) := sorry

/-- The graph adapter's cut value equals the original satisfied edge fraction.
[OD14, §11.7, Max-Cut objective]
**Proof sketch.** Count both orientations of each original edge in the weighted
sum. Symmetric cut indicators cancel the factor of two in the denominator. -/
theorem maxCutGraph_cutValue (E : List (ℕ × ℕ))
    (F : Fin (maxCutVertexBound E) → Bool) (f : ℕ → Bool)
    (hF : ∀ v, F v = f v.val) :
    MaxCut.cutValue (maxCutGraph E) F =
      ((E.filter fun e => f e.1 ≠ f e.2).length : ℝ) / (E.length : ℝ) := sorry

/-- Promise NP-hardness implies the existing language NP-hardness for every
language that separates the two promises. [OD14, §7.3; AB09, §2.2]

**Proof sketch.** For each NP language, use its promise reduction. Membership
and nonmembership land on opposite sides of the separating language, giving
the existing many-one reducibility contract. -/
theorem PromiseNPHard.separating_language {Y N L : Language Bool}
    (h : PromiseNPHard Y N) (hY : ∀ x, x ∈ Y → x ∈ L) (hN : Disjoint N L) :
    Complexity.NPHard L := sorry

/-- Assuming the Unique Games Conjecture, approximating Max-Cut beyond the
Goemans–Williamson curve is NP-hard. [OD14, Thm. 11.74; KKMO07]
The source's phrase "UG-hard" is expanded as NP-hardness conditional on UGC.
The reduction uses the project's concrete polynomial-time machine predicate.
The explicit threshold gap specifies the proper nonoverlapping promise regime;
the following separating-language theorem retains all positive source losses.

**Proof sketch.** The negative-correlation noise-sensitivity test has dictator
acceptance `(1-cos θ)/2`; Majority Is Stablest bounds its no-notables acceptance
by `θ/π`. Apply the Unique Games-to-test reduction. Perturb the angle slightly
as in Exercise 11.36 to absorb completeness losses and rational approximation
of fixed probabilities; repeated constraints implement the rational weights,
and the duplicate-query correction gives loop-free finite inputs. -/
theorem maxCut_ug_hard {θ δ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 2) Real.pi) (hδ : 0 < δ)
    (hgap : θ / Real.pi + δ < (1 - Real.cos θ) / 2)
    (hUGC : UniqueGamesConjecture) :
    PromiseNPHard (maxCutYes ((1 - Real.cos θ) / 2))
      (maxCutNo (θ / Real.pi + δ)) := sorry

/-- For every positive additive loss in the source theorem, any language
separating the Max-Cut completeness and soundness thresholds is NP-hard under
UGC. [OD14, Thm. 11.74; KKMO07]
This retains the source's unrestricted `δ > 0`: if the thresholds overlap,
no separating language exists. The preceding proper-promise version makes
the nonoverlapping gap hypothesis explicit.

**Proof sketch.** In the nonoverlapping regime apply the Unique Games test
reduction and the promise-to-language bridge. At coinciding or overlapping
thresholds use the same reduction with a smaller positive loss whose NO set
is contained in the requested NO set. -/
theorem maxCut_ug_hard_separating_language {θ δ : ℝ}
    (hθ : θ ∈ Set.Ioo (Real.pi / 2) Real.pi) (hδ : 0 < δ)
    (hUGC : UniqueGamesConjecture) (L : Language Bool)
    (hY : ∀ x, x ∈ maxCutYes ((1 - Real.cos θ) / 2) → x ∈ L)
    (hN : Disjoint (maxCutNo (θ / Real.pi + δ)) L) :
    Complexity.NPHard L := sorry

end BooleanAnalysis.GaussianSpace.UniqueGames
