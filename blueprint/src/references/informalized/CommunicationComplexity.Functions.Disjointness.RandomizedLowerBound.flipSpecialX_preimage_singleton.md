<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.flipSpecialX_preimage_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Preimage Under an Involution

**Claim.** For every hard sample $\omega$, the preimage of $\{\omega\}$ under the special-bit flip is the singleton containing the flipped sample.

**Proof.** To prove equality of the two sets, test an arbitrary sample $\eta$. If $\eta$ lies in the preimage, then flipping $\eta$ gives $\omega$. Flipping both sides once more and using that the flip is an involution shows $\eta=\phi(\omega)$, so $\eta$ belongs to the proposed singleton. Conversely, if $\eta=\phi(\omega)$, then applying the flip to $\eta$ gives $\omega$, again by involutivity; hence $\eta$ lies in the preimage.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.flipSpecialX_flipSpecialX`.
