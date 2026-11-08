<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.signTwistTranscript_transcript -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Twisting a Tester Transcript

**Claim.** For a fixed seed, multiplying each answered query value by the phase at its query point produces exactly the transcript obtained by querying the pointwise product of the input and phase.

**Proof.** Fix a transcript position $j$. The transcript value there is the queried address mapped through the input function (`NonadaptiveFunctionTester.transcript_apply`). If there is no query address, both transcripts have no value at this position. If the address is $x$, the twisted transcript returns the input value $f(x)$ multiplied by $\mathrm{phase}(x)$, which is exactly the value of the pointwise product function at $x$. Hence the two transcripts agree at every position, and so are equal.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
