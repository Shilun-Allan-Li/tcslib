<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.repeatAndFunctionTester_componentTranscript -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transcript of a repeated component

**Claim.** For any seed tuple and component $i$, the repeated tester's transcript at the query positions belonging to component $i$ is exactly the transcript of $T$ on $f$ with seed $s_i$.

**Proof.** Fix a transcript position $j$ in the component. Under the repeated tester's query arrangement, the position corresponding to $(i,j)$ is assigned the query that $T$ makes at position $j$ using seed $s_i$. Applying $f$ to that query gives the same answer as in $T$'s transcript at $j$. Hence the transcripts agree at every position and are equal as functions.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
