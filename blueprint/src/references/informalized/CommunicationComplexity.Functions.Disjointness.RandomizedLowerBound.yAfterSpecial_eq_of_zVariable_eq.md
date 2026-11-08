<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yAfterSpecial_eq_of_zVariable_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering the post-special profile

**Claim.** If an achievable value of $Z$ is produced by a sample $\omega$, then that sample’s post-special vector equals the $Y_{>T}$ component of the value.

**Proof.** Apply the projection that sends each value of $Z$ to its $y_{>T}$ component to the equality asserting that $\omega$ produces $z$. The left side is the post-special vector of $\omega$ by the definition of the produced value, and the right side is the component $z.yAfter$. Thus the two vectors agree.
