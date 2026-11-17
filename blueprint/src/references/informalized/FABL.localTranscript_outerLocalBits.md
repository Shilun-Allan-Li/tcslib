<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.localTranscript_outerLocalBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transcript from Outer Query Bits

**Claim.** For every input word, proof word, and verifier seed, the local transcript from the outer query bits equals the transcript obtained by querying the combined input and proof word.

**Proof.** Compare the two transcripts at an arbitrary query position. The tester’s transcript at that position is its query address mapped through the combined input and proof word (NonadaptiveFunctionTester.transcript_apply). If the query is absent, both transcripts are absent. If it is present at an address, the outer query bit is defined by evaluating the combined word at that address: the default address in the definition of the outer query address is irrelevant in this present-query case. Mapping the present address through that bit therefore gives exactly the combined word’s value there. The transcripts agree at every position, hence are equal.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
