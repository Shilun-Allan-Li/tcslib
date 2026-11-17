<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.twoQuery_embeddedMajority_transcript_eq_dictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching Dictator Transcript

**Claim.** For every odd $d\le n$ and every seed, some coordinate dictator has exactly the same two-query transcript as majority on the first $d$ coordinates.

**Proof.** Fix a seed and fill each missing query address with the constant $+1$ input, obtaining two total inputs $x$ and $y$. The common majority-agreement coordinate lemma (`FABL.exists_common_majorityAgreementCoordinate`) gives an index $i<d$ where each input's value at coordinate $i$ equals its majority value on the first $d$ coordinates. Use the corresponding coordinate $i<n$ for the dictator. At either query position, if the query is absent, both transcripts have no answer. If the query is an input $q$, the agreement property says that the dictator's answer $q_i$ equals the embedded-majority answer. Since a transcript entry is the queried function's value when the query is present (`FABL.NonadaptiveFunctionTester.transcript_apply`), the entries agree at both positions, hence the transcripts are equal.

**Key facts.** `FABL.exists_common_majorityAgreementCoordinate`, `FABL.NonadaptiveFunctionTester.transcript_apply`.
