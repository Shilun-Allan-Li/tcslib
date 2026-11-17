<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.singletonTrueString_transcript_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transcript Invariance at an Unqueried Coordinate

**Claim.** If a seed's query positions never address coordinate $i$, then the transcript on the string true only at $i$ equals the transcript on the constantly false string.

**Proof.** Compare the transcripts at each query position. By the transcript formula (`NonadaptiveFunctionTester.transcript_apply`), each entry is the queried address with the input string applied, when an address is present. If no address is present, both entries are empty. If the address is some coordinate $k$, the hypothesis that the seed never queries $i$ implies $k\ne i$. Both strings are false at $k$, so the entries agree. Since they agree at every position, the transcripts are equal.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
