<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mix_mem_fiber_inter_specialPair_of_mem_specialX_specialY -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mixing Preserves the Fiber and Special Pair

**Claim.** If two samples lie in the same fiber, and their Alice and Bob special-coordinate bits are respectively $b_X$ and $b_Y$, then mixing Alice’s data from the first with Bob’s data from the second yields a sample in that fiber with special pair $(b_X,b_Y)$.

**Proof.** The fiber assumptions give $Z(\omega_X)=z$ and $Z(\omega_Y)=z$. Mixing samples with the same value of $Z$ preserves that value (`zVariable_mix_eq_of_same_zVariable`), so the mixture remains in the fiber over $z$. The mixture keeps Alice’s special bit from $\omega_X$ (`specialX_mix`) and Bob’s special bit from $\omega_Y$ (`specialY_mix`); these are $b_X$ and $b_Y$ by hypothesis. Hence its special pair is $(b_X,b_Y)$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_mix_eq_of_same_zVariable`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialX_mix`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialY_mix`.
