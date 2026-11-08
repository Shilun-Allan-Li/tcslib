<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/RectangleSwitching.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.input_mem_transcript_of_zVariable_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input lies in the specified transcript class

**Claim.** If a hard sample has $Z$-value $z$, then its input pair belongs to the transcript class specified by the transcript component of $z$.

**Proof.** The equality of $Z$-values implies that the transcript component of $z$ is the transcript produced by the protocol on the sample's input. For that input, the protocol transcript membership property guarantees that the input lies in the class of pairs following its transcript (`input_mem_transcript`). Substituting the equal transcript components gives the desired membership.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.input_mem_transcript`.
