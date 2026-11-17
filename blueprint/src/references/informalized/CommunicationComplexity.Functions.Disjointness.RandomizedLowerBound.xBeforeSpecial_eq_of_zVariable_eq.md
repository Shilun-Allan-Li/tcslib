<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_eq_of_zVariable_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering Pre-Special Bits

**Claim.** For any sample whose statistic equals $z$, its padded before-special Alice vector equals the before-special component of $z$.

**Proof.** Apply the function that extracts the before-special component to the equality between the sample’s statistic and $z$. Equality is preserved by applying a function, so the extracted components agree. Unfolding the statistic shows that the sample’s component is exactly its before-special vector.
