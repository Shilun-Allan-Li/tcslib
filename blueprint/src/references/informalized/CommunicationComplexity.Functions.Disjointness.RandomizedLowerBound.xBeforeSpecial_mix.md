<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_mix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mixing Preserves the Before-Special Vector

**Claim.** Under the stated agreement hypotheses, the mixed sample has the same before-special vector as $\omega_X$.

**Proof.** Compare the vectors at an arbitrary coordinate $i$. If $i<T$, the bit of Alice’s input in the mixed sample agrees with her bit in $\omega_X$ by the preservation-of-Alice-bits result (`xBit_mix`); the shared special coordinate lets us apply that result with the stated hypotheses. If $i\not<T$, both padded vectors are false at $i$. Hence the vectors agree everywhere.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_mix`.
