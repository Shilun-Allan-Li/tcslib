<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.reindexDomainFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability Under Domain Reindexing

**Claim.** The reindexed tester's acceptance probability on $f$ equals the original tester's acceptance probability on $f\circ e$.

**Proof.** Both acceptance probabilities average, over the same seed distribution, the indicator that the tester accepts its transcript. Fix a seed. At each query position, the reindexed tester maps the original query address through $e$ and then evaluates $f$; this is exactly evaluation of $f\circ e$ at the original query address. The transcript formula (`FABL.NonadaptiveFunctionTester.transcript_apply`) makes this equality explicit, including positions with no query. Thus the two transcripts agree at every position, the acceptance decisions agree for each seed, and averaging their identical indicators gives the claimed equality.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
