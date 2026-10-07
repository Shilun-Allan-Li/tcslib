<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/RoundTrip.lean :: razborovEncode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Razborov encoding is injective on bad restrictions

**Claim.** Let `f` have width ≤ `w` and variable-distinct literals within each
clause (`hnd`), and let `ρ₁, ρ₂` both be bad for depth `d`
(`IsBadRestriction f.eval d`). If `razborovEncode f w d ρ₁ = razborovEncode f w d ρ₂`
then `ρ₁ = ρ₂`.

**Proof.** Immediate from the round-trip: `rw [← razborovDecode_encode … ρ₁ hbad₁ hw hnd,
← razborovDecode_encode … ρ₂ hbad₂ hw hnd, henc]` — rewrite each `ρᵢ` as
`razborovDecode` of its own encoding, then rewrite the two encodings into each
other with `henc`.

**Used in.** `fiber_bound` (`TCSlib/BooleanAnalysis/Switching.lean`): injectivity
makes `ρ ↦ (razborovEncode f w d ρ).2` an injection on the fiber of bad
restrictions over a fixed `γ`, whose image is then counted by `aux_image_card_bound`
to give the `(4w)^d` bound.
