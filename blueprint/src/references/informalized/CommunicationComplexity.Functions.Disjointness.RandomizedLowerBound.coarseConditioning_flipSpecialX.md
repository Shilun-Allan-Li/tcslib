<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coarseConditioning_flipSpecialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coarse Conditioning Is Flip Invariant

**Claim.** Toggling Alice’s bit at the special coordinate leaves the coarse conditioning $(T,X_{<T},Y_{>T})$ unchanged.

**Proof.** The special coordinate remains $T$ under the flip. The preceding lemma for Alice’s bits shows that $X_{<T}$ is unchanged (xBeforeSpecial_flipSpecialX): the flip changes only the bit at $T$, outside the strictly lower coordinates. The corresponding lemma for Bob’s bits shows that $Y_{>T}$ is unchanged (yAfterSpecial_flipSpecialX), since neither Bob’s bit nor any other coordinate type is altered. Thus all three components of the coarse conditioning agree.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_flipSpecialX`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yAfterSpecial_flipSpecialX`.
