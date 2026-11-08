<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mix_mem_fiber_inter_specialY_of_mem_fiber_specialPair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mixing Preserves the Fiber and Bob’s Bit

**Claim.** If two samples lie in the same fiber and the second has special pair $b$, then mixing Alice’s input from the first with Bob’s input from the second remains in that fiber and has Bob special bit $b_2$.

**Proof.** Both samples have $Z=z$, so mixing them preserves this value (`zVariable_mix_eq_of_same_zVariable`) and hence stays in the fiber. The second sample’s special pair is $b$, whose Bob component is $b_2$. Mixing preserves Bob’s special bit from the second sample (`specialY_mix`), proving the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_mix_eq_of_same_zVariable`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialY_mix`.
