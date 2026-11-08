<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.boolTruthTableLiftTester_visibleTranscript -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transcript of the Lifted Tester

**Claim.** For every seed, converting each answer in the lifted tester’s transcript on $(w,p)$ from a Boolean value to a sign gives the transcript of $T$ on the sign-valued function encoded by $p$.

**Proof.** Fix a transcript position $j$. By the definition of a tester’s transcript, its entry is the query at position $j$ with the input function applied, if a query is present. Split according to whether $T$ makes a query there. If there is no query, both transcripts have no answer. If the query is a sign vector $x$, the lifted query points to the proof-table entry indexed by $x$; the concatenated input therefore returns $p$ at that index. Converting this Boolean answer to a sign gives the value of the encoded function at $x$. Thus the transcript entries agree at every position, proving equality of transcripts.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
