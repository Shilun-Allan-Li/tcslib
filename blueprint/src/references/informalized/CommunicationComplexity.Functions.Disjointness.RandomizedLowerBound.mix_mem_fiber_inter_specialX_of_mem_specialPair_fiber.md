<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.mix_mem_fiber_inter_specialX_of_mem_specialPair_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mixing Preserves the Fiber and Alice’s Bit

**Claim.** If a sample with special pair $b$ and another sample lie in the same fiber, mixing Alice’s input from the first with Bob’s input from the second stays in that fiber and has Alice special bit $b_1$.

**Proof.** The two fiber assumptions say that both samples have $Z=z$. The mixing property for samples with equal $Z$ values (`zVariable_mix_eq_of_same_zVariable`) therefore puts their mixture in the fiber over $z$. The first sample’s special pair is $b$, so its Alice component is $b_1$. Mixing preserves Alice’s special bit from the first sample (`specialX_mix`), giving the claimed bit.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_mix_eq_of_same_zVariable`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialX_mix`.
