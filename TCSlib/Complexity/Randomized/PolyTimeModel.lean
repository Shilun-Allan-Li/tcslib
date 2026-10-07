/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SipserGacs
import TCSlib.Complexity.Randomized.Adleman
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.PolyHierarchy.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The polynomial-time verifier model

The instantiation of `Randomized.VerifierModel` by genuine polynomial-time
Turing machines, now that the Chapter 1–2 development (`Complexity.P`,
`Complexity.PolyTimeComputable`, `Turing.pairEncode`, `Complexity.SigmaP`)
is on `main`.  This connects the abstract Chapter 7 class theorems to the
book's machine-based statements: each `ClosedUnder…` hypothesis becomes a
lemma about `P`, and the certificate-style `Σ₂` coincides with
`Complexity.SigmaP 2`.

## Main definitions

* `Randomized.polyTimeModel` — the `VerifierModel` whose efficient verifiers
  are those computed by a `P`-language on the `Turing.pairEncode`d input.

## Main results (sorry-stubbed)

* `Randomized.polyTimeModel_closedUnderRace` /
  `…_closedUnderAnswerIs` / `…_closedUnderMajority` / `…_closedUnderAny` /
  `…_closedUnderNot` / `…_closedUnderShiftOr` — the closure hypotheses of
  `Randomized.Classes` and `Randomized.SipserGacs` hold for polynomial time.
* `Randomized.inSigma2_polyTimeModel_iff` — certificate-style `Σ₂` for the
  poly-time model coincides with `Complexity.SigmaP 2`.
* `Randomized.zpp_eq_rp_inter_corp_polyTime`,
  `Randomized.sipser_gacs_polyTime` — [AB09, Thm 7.8] and [AB09, Thm 7.18]
  for polynomial-time machines, with no abstract hypotheses.

## Deviations from the source

None beyond those of `Randomized.Classes`: these declarations *discharge*
the deviations by instantiating the abstract model.  With the library's
`Complexity.P_subset_PPoly` ([AB09, Thm 6.6]) now available, Adleman's
circuit hypothesis is dischargeable too
(`Randomized.polyTimeModel_verifierHasCircuits`), so [AB09, Thm 7.17] is
stated unconditionally as `Randomized.adleman_polyTime`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Complexity

/-- The polynomial-time verifier model: a verifier is *efficient* when its
output is computed by `P`-languages on the `Turing.pairEncode`d pair of
input and random string (`some true`-set and `some false`-set each in `P`),
and a two-witness predicate is efficient when its truth set, on the nested
pairing used by `Complexity.SigmaP`, is in `P`.  This is "`M` is a
polynomial-time TM" of [AB09, Def 7.4], in the library's encoding
conventions. -/
noncomputable def polyTimeModel : VerifierModel where
  Eff M := ∃ V₁ V₀ : Language Bool, V₁ ∈ P ∧ V₀ ∈ P ∧
    ∀ x r : List Bool,
      (M x r = some true ↔ Turing.pairEncode x r ∈ V₁) ∧
      (M x r = some false ↔ Turing.pairEncode x r ∈ V₀)
  EffTwoWitness N := ∃ V : Language Bool, V ∈ P ∧
    ∀ x u v : List Bool,
      (N x u v = true ↔ Turing.pairEncode (Turing.pairEncode x u) v ∈ V)

/-- Polynomial time is closed under the race construction.
**Proof sketch.** Decode the pair, split the random string at the
(poly-time computable) point `polyLen a k |x|`, run both `P`-verifiers
(`Complexity.PClosure`-style composition), and combine the answers; each
output set is a `P`-language by closure of `P` under the pairing plumbing
of `Complexity.PolyTimePairing`. -/
theorem polyTimeModel_closedUnderRace : ClosedUnderRace polyTimeModel := by
  sorry

/-- Polynomial time is closed under the output-postprocessing construction.
**Proof sketch.** The `some b`-set of `M` is literally one of the two
`P`-languages witnessing `Eff M`. -/
theorem polyTimeModel_closedUnderAnswerIs :
    ClosedUnderAnswerIs polyTimeModel := by
  sorry

/-- Polynomial time is closed under polynomial majority repetition.
**Proof sketch.** A counting loop over `polyLen a' k' |x|` blocks, each
block a run of the `P`-verifier on a poly-time-extractable slice of the
random string; the vote count and the final comparison are poly-time
(`Complexity.CounterProgPolyTime`). -/
theorem polyTimeModel_closedUnderMajority :
    ClosedUnderMajority polyTimeModel := by
  sorry

/-- Polynomial time is closed under polynomial `OR`-repetition.
**Proof sketch.** As for the majority closure, with the vote count replaced
by a single accepting flag. -/
theorem polyTimeModel_closedUnderAny : ClosedUnderAny polyTimeModel := by
  sorry

/-- Polynomial time is closed under negating the verifier's answer.
**Proof sketch.** Swap the two witnessing `P`-languages. -/
theorem polyTimeModel_closedUnderNot : ClosedUnderNot polyTimeModel := by
  sorry

/-- Polynomial time recognizes the shifted-OR construction.
**Proof sketch.** Decode the nested pair, slice `u` into its
`polyLen a' k' |x|` shift blocks, XOR each with `v` (bitwise XOR of
equal-length lists is poly-time), run the `P`-verifier on each, and `OR`
the results. -/
theorem polyTimeModel_closedUnderShiftOr :
    ClosedUnderShiftOr polyTimeModel := by
  sorry

/-- Polynomial-time verifiers have polynomial-size circuits when their
random string is fixed, with one size bound uniform in the random string:
the form of [AB09, Thm 6.6] that Adleman's counting argument consumes.
**Proof sketch.** The paired language of the verifier is in `P`, so by the
tableau construction behind `Complexity.P_subset_PPoly` it has a fan-in-two
circuit family of size polynomial in the padded input length
`|pairEncode x r|` — polynomial in `|x|` since `|r| = polyLen a k |x|`.
Hardwire the `r`-input wires of the circuit for length `|pairEncode x r|`
to the bits of `r` (`CircuitComplexity.HardWire`); the size bound is
inherited from the family, hence uniform in `r`. -/
theorem polyTimeModel_verifierHasCircuits :
    ∀ M a k, polyTimeModel.Eff (boolVerifier M) →
      VerifierHasCircuits M (polyLen a k) := by
  sorry

/-- **Adleman's theorem for polynomial-time machines** ([AB09, Thm 7.17],
unconditionally): `BPP ⊆ P/poly`, with both sides the library's own classes
(`InBPP polyTimeModel` and `Language.InPPoly`). -/
theorem adleman_polyTime {L : Language Bool}
    (hL : InBPP polyTimeModel L) : L.InPPoly :=
  adleman polyTimeModel polyTimeModel_closedUnderMajority hL
    polyTimeModel_verifierHasCircuits

/-- Certificate-style `Σ₂` over the polynomial-time model coincides with the
library's `Complexity.SigmaP 2` ([AB09, Definition 5.3]).
**Proof sketch.** Both say: a `P`-predicate of the nested pair
`⟨⟨x, u⟩, v⟩` with `∃ u ∀ v` over blocks of length `C·(|x|+1)^c`.  The two
length normal forms (`polyLen a k` here, `C·(n+1)^c` in `PolyHierarchy`)
are identical, so the translation is a re-bracketing of the quantifiers
plus padding of the two block lengths to a common bound. -/
theorem inSigma2_polyTimeModel_iff (L : Language Bool) :
    InSigma2 polyTimeModel L ↔ L ∈ SigmaP 2 := by
  sorry

/-- **`ZPP = RP ∩ coRP` for polynomial-time machines** ([AB09, Thm 7.8],
unconditionally): the abstract theorem at `polyTimeModel`, with every
closure hypothesis discharged. -/
theorem zpp_eq_rp_inter_corp_polyTime (L : Language Bool) :
    InZPP polyTimeModel L ↔ InRP polyTimeModel L ∧ InCoRP polyTimeModel L :=
  inZPP_iff_inRP_and_inCoRP polyTimeModel polyTimeModel_closedUnderRace
    polyTimeModel_closedUnderAnswerIs polyTimeModel_closedUnderAny L

/-- **Sipser–Gács for polynomial-time machines** ([AB09, Thm 7.18],
unconditionally): `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` with the library's own polynomial
hierarchy (`Complexity.SigmaP`/`Complexity.PiP`).

**Proof sketch.** The abstract `sipser_gacs` at `polyTimeModel` with its
closure hypotheses discharged, transported along
`inSigma2_polyTimeModel_iff` (and its complement instance for the `Π₂`
half). -/
theorem sipser_gacs_polyTime {L : Language Bool}
    (hL : InBPP polyTimeModel L) :
    L ∈ SigmaP 2 ∧ L ∈ PiP 2 := by
  sorry

end Randomized
