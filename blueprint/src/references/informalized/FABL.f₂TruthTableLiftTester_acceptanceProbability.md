<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.f₂TruthTableLiftTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability of a lifted tester

**Claim.** The lifted tester's acceptance probability on the word formed from $w$ and the truth table of $p$ equals the original tester's acceptance probability on the function encoded by $p$.

**Proof.** Expand both probabilities as expectations over the same seed distribution. It is enough to verify that for every seed and transcript position the lifted tester supplies exactly the answer that the original tester receives from the function encoded by $p$. If the original query is absent, both transcripts have no answer. If it queries $x\in\mathbb F_2^d$, the lifted query points to the truth-table location representing $x$; the word supplies there the bit $p$ at that location, and the lifted tester converts that bit to its corresponding sign. By definition, this is precisely the value of the function encoded by $p$ at $x$. Thus the transcripts and acceptance decisions coincide for every seed, so the expectations agree.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`.
