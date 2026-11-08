<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddWeightShortProofPCPPSystem_transcript -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Verifier Transcripts

**Claim.** For every input word $w$, proof word $p$, and seed, restoring a true value at any query to the omitted final proof position makes the short-proof verifier's transcript equal to the partial-sum verifier's transcript on the proof extended by a final true bit.

**Proof.** Compare the transcript at each of the three query positions, splitting first by the seed type. For the initial-check seed, the two input queries are unchanged, and the proof query at position zero is retained; the restoration fact for an ordinary proof query (\texttt{restoreFinalTrueProofValue\_omit\_proof}) identifies its value with the corresponding value in the extended proof. For the final-check seed, its only query is to the omitted last proof position: the short verifier has no such query, and restoration inserts true, exactly the appended proof bit; the other two positions are empty in both transcripts. For a step seed $k$, the first and third queries are proof positions $k$ and $k+1$, respectively. The restoration fact identifies their restored values with those in the extended proof, while the middle input query is unchanged. Hence every coordinate of the transcripts agrees. The interpretation of a transcript entry as the queried word value is the defining rule for transcripts (\texttt{NonadaptiveFunctionTester.transcript\_apply}).

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`, `FABL.restoreFinalTrueProofValue_omit_proof`.
