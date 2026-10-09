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
import TCSlib.Complexity.PolyHierarchy.Normalize
import TCSlib.Complexity.PolyHierarchy.Collapse

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

/-- Keep the input `x` and the first `polyLen a k |x|` bits of the random
string: the pair-level reindexing behind the race and shifted constructions.
On `Turing.pairEncode x r` it returns `Turing.pairEncode x (r.take (polyLen a k |x|))`. -/
def sliceTake (a k : ℕ) (z : List Bool) : List Bool :=
  Turing.pairEncode (pairFstD z) ((pairSndD z).take (polyLen a k (pairFstD z).length))

/-- Keep the input `x` and drop the first `polyLen a k |x|` bits of the random
string.  On `Turing.pairEncode x r` it returns
`Turing.pairEncode x (r.drop (polyLen a k |x|))`. -/
def sliceDrop (a k : ℕ) (z : List Bool) : List Bool :=
  Turing.pairEncode (pairFstD z) ((pairSndD z).drop (polyLen a k (pairFstD z).length))

/-- Take, from the second component of a pair, a prefix as long as the first
component: on `Turing.pairEncode u s` it returns `s.take |u|`.  The
length-gated prefix primitive underlying `sliceTake` (and the block slicing of
the shifted construction); the polynomial `polyLen a k` enters only through the
unary length `u`, so no in-machine exponentiation is needed. -/
def takePrefixByLen (p : List Bool) : List Bool := (pairSndD p).take (pairFstD p).length

/-- Drop, from the second component of a pair, a prefix as long as the first
component: on `Turing.pairEncode u s` it returns `s.drop |u|`. -/
def dropPrefixByLen (p : List Bool) : List Bool := (pairSndD p).drop (pairFstD p).length

/-- `takePrefixByLen` is polynomial-time computable.
**Proof sketch.** A single left-to-right pass (`Complexity.CounterProg`):
mirror `Turing.pairDecode` over the doubled first component, counting its
length `|u|` into a register; at the separator, copy the second component
while the register counts down, truncating once it reaches zero.  Malformed
inputs (`pairDecode = none`) halt with empty output, matching
`pairFstD`/`pairSndD = []`.  The abstract step count is linear in `|p|`, so
`Complexity.CounterProg.polyTimeComputable` applies. -/
theorem polyTimeComputable_takePrefixByLen : PolyTimeComputable takePrefixByLen := by
  sorry

/-- `dropPrefixByLen` is polynomial-time computable.
**Proof sketch.** As `takePrefixByLen`, but the copy phase emits only after the
length register has counted down past the first `|u|` bits of the second
component. -/
theorem polyTimeComputable_dropPrefixByLen : PolyTimeComputable dropPrefixByLen := by
  sorry

/-- `sliceTake a k` is polynomial-time computable.
**Proof.** `polyLen a k |x| = a·(|x|+1)^k` is available as a *unary* string via
`Complexity.polyTimeComputable_polyUnary`; pair it with the random string and
apply `takePrefixByLen`, which truncates to that length without any in-machine
exponentiation. -/
theorem polyTimeComputable_sliceTake (a k : ℕ) :
    PolyTimeComputable (sliceTake a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (polyLen a k (pairFstD z).length) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => Turing.pairEncode
      (List.replicate (polyLen a k (pairFstD z).length) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).take (polyLen a k (pairFstD z).length)) := by
    have heq : (fun z => (pairSndD z).take (polyLen a k (pairFstD z).length)) =
        takePrefixByLen ∘ (fun z => Turing.pairEncode
          (List.replicate (polyLen a k (pairFstD z).length) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, takePrefixByLen, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate]
    rw [heq]
    exact polyTimeComputable_takePrefixByLen.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-- `sliceDrop a k` is polynomial-time computable.
**Proof.** As `sliceTake`, with `dropPrefixByLen` in place of
`takePrefixByLen`. -/
theorem polyTimeComputable_sliceDrop (a k : ℕ) :
    PolyTimeComputable (sliceDrop a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (polyLen a k (pairFstD z).length) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => Turing.pairEncode
      (List.replicate (polyLen a k (pairFstD z).length) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).drop (polyLen a k (pairFstD z).length)) := by
    have heq : (fun z => (pairSndD z).drop (polyLen a k (pairFstD z).length)) =
        dropPrefixByLen ∘ (fun z => Turing.pairEncode
          (List.replicate (polyLen a k (pairFstD z).length) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, dropPrefixByLen, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate]
    rw [heq]
    exact polyTimeComputable_dropPrefixByLen.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-- Polynomial time is closed under the race construction.
**Proof.** The `some true`-set of the race is the preimage of `M₁`'s
`some true`-set `V₁` under `sliceTake a k`, and the `some false`-set is the
intersection of the complement of that preimage with the preimage of `M₂`'s
`some true`-set `V₂` under `sliceDrop a k`; both are in `P` by
`Complexity.preimage_mem_P`, `Complexity.compl_mem_P`, and
`Complexity.inter_mem_P`, once `sliceTake`/`sliceDrop` are polynomial-time
(`polyTimeComputable_sliceTake`/`_sliceDrop`).  The off-pair freedom in the
efficiency notion lets us use these preimages verbatim. -/
theorem polyTimeModel_closedUnderRace : ClosedUnderRace polyTimeModel := by
  rintro M₁ M₂ a k ⟨V₁, _, hV₁, _, hM₁⟩ ⟨V₂, _, hV₂, _, hM₂⟩
  refine ⟨sliceTake a k ⁻¹' V₁,
    {z | z ∈ (sliceTake a k ⁻¹' V₁)ᶜ ∧ z ∈ sliceDrop a k ⁻¹' V₂},
    preimage_mem_P hV₁ (polyTimeComputable_sliceTake a k),
    inter_mem_P (compl_mem_P (preimage_mem_P hV₁ (polyTimeComputable_sliceTake a k)))
      (preimage_mem_P hV₂ (polyTimeComputable_sliceDrop a k)),
    fun x r => ?_⟩
  have hv1 : (Turing.pairEncode x r ∈ sliceTake a k ⁻¹' V₁) ↔
      M₁ x (r.take (polyLen a k x.length)) = true := by
    simp only [Set.mem_preimage, sliceTake, pairFstD_pairEncode, pairSndD_pairEncode]
    have h := (hM₁ x (r.take (polyLen a k x.length))).1
    simp only [boolVerifier, Option.some.injEq] at h
    exact h.symm
  have hv2 : (Turing.pairEncode x r ∈ sliceDrop a k ⁻¹' V₂) ↔
      M₂ x (r.drop (polyLen a k x.length)) = true := by
    simp only [Set.mem_preimage, sliceDrop, pairFstD_pairEncode, pairSndD_pairEncode]
    have h := (hM₂ x (r.drop (polyLen a k x.length))).1
    simp only [boolVerifier, Option.some.injEq] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · rw [hv1]
    cases h1 : M₁ x (r.take (polyLen a k x.length)) <;>
      cases h2 : M₂ x (r.drop (polyLen a k x.length)) <;>
      simp [raceVerifier, h1, h2]
  · rw [Set.mem_setOf_eq, Set.mem_compl_iff, hv1, hv2]
    cases h1 : M₁ x (r.take (polyLen a k x.length)) <;>
      cases h2 : M₂ x (r.drop (polyLen a k x.length)) <;>
      simp [raceVerifier, h1, h2]

/-- Polynomial time is closed under the output-postprocessing construction.
**Proof.** The `some b`-set of `M` is literally one of the two
`P`-languages witnessing `Eff M`, and the `some (!b)`-set of the resulting
Boolean verifier is its complement (`Complexity.compl_mem_P`). -/
theorem polyTimeModel_closedUnderAnswerIs :
    ClosedUnderAnswerIs polyTimeModel := by
  rintro M b ⟨V₁, V₀, hV₁, hV₀, hM⟩
  cases b
  · refine ⟨V₀, V₀ᶜ, hV₀, compl_mem_P hV₀, fun x r => ?_⟩
    have h := (hM x r).2
    constructor
    · show some (decide (M x r = some false)) = some true ↔ _
      simp only [Option.some.injEq, decide_eq_true_eq]
      exact h
    · show some (decide (M x r = some false)) = some false ↔ _
      simp only [Option.some.injEq, decide_eq_false_iff_not]
      rw [h]
      exact Iff.rfl
  · refine ⟨V₁, V₁ᶜ, hV₁, compl_mem_P hV₁, fun x r => ?_⟩
    have h := (hM x r).1
    constructor
    · show some (decide (M x r = some true)) = some true ↔ _
      simp only [Option.some.injEq, decide_eq_true_eq]
      exact h
    · show some (decide (M x r = some true)) = some false ↔ _
      simp only [Option.some.injEq, decide_eq_false_iff_not]
      rw [h]
      exact Iff.rfl

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
**Proof.** Swap the two witnessing `P`-languages. -/
theorem polyTimeModel_closedUnderNot : ClosedUnderNot polyTimeModel := by
  rintro M ⟨V₁, V₀, hV₁, hV₀, hM⟩
  refine ⟨V₀, V₁, hV₀, hV₁, fun x r => ?_⟩
  have h := hM x r
  simp only [boolVerifier, Option.some.injEq] at h ⊢
  rw [Bool.not_eq_true', Bool.not_eq_false']
  exact ⟨h.2, h.1⟩

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
  classical
  constructor
  · rintro ⟨N, a₁, k₁, a₂, k₂, ⟨V, hV, hN⟩, hiff⟩
    have h₁ : PolyHierarchy.UnaryPT
        (fun y : List Bool => polyLen a₁ k₁ y.length) := by
      have h := PolyHierarchy.unaryPT_poly a₁ k₁ polyTimeComputable_id
      simpa [polyLen] using h
    have h₂ : PolyHierarchy.UnaryPT
        (fun y : List Bool => polyLen a₂ k₂ y.length) := by
      have h := PolyHierarchy.unaryPT_poly a₂ k₂ polyTimeComputable_id
      simpa [polyLen] using h
    have hmem := PolyHierarchy.mem_altClass_of_normal (b := true) (i := 1)
      hV polyTimeComputable_id h₁ h₂
    have hkey : L = {y | qStep true (polyLen a₁ k₁ y.length)
        fun U => altQuant V (polyLen a₂ k₂ y.length) false 1
          (id (Turing.pairEncode y U))} := by
      ext y
      rw [Set.mem_setOf_eq, hiff y]
      constructor
      · rintro ⟨u, hu, hall⟩
        refine ⟨u, hu, fun v hv => ?_⟩
        show Turing.pairEncode (Turing.pairEncode y u) v ∈ V
        exact (hN y u v).mp (hall v hv)
      · rintro ⟨u, hu, hall⟩
        refine ⟨u, hu, fun v hv => ?_⟩
        exact (hN y u v).mpr (hall v hv)
    rw [hkey]
    exact hmem
  · intro hL
    obtain ⟨C, c, V, hV, hiff⟩ := mem_SigmaP_two_iff_exists_forall.mp hL
    refine ⟨fun x u v =>
        decide (Turing.pairEncode (Turing.pairEncode x u) v ∈ V),
      C, c, C, c,
      ⟨V, hV, fun x u v => by rw [decide_eq_true_eq]⟩, fun x => ?_⟩
    rw [hiff x]
    constructor
    · rintro ⟨u, hu, hall⟩
      refine ⟨u, hu, fun v hv => ?_⟩
      rw [decide_eq_true_eq]
      exact hall v hv
    · rintro ⟨u, hu, hall⟩
      refine ⟨u, hu, fun v hv => ?_⟩
      have h := hall v hv
      rw [decide_eq_true_eq] at h
      exact h

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
  obtain ⟨h1, h2⟩ := sipser_gacs polyTimeModel
    polyTimeModel_closedUnderMajority polyTimeModel_closedUnderNot
    polyTimeModel_closedUnderShiftOr hL
  exact ⟨(inSigma2_polyTimeModel_iff L).mp h1,
    (inSigma2_polyTimeModel_iff Lᶜ).mp h2⟩

end Randomized
