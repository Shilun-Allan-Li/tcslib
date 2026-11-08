<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.naeTest_levelOneWeight_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NAE test and level-one weight

**Claim.** If the NAE test accepts the Boolean function with probability $1-\varepsilon$, then its level-one Fourier weight satisfies $1-\frac{9}{2}\varepsilon\le W_1[f]$.

**Proof.** The Condorcet-winner probability is at most $\frac79+\frac29 W_1[f]$ (\texttt{FABL.condorcetWinnerProbability_le}). The acceptance probability of the NAE tester equals this Condorcet-winner probability (\texttt{FABL.naeFunctionTester_acceptanceProbability}); substituting the assumed acceptance probability gives $1-\varepsilon\le\frac79+\frac29W_1[f]$. Rearranging yields $1-\frac92\varepsilon\le W_1[f]$.

**Key facts.** `FABL.condorcetWinnerProbability_le`, `FABL.naeFunctionTester_acceptanceProbability`.

**Caveat.** The stated FKN consequence is not part of the formal theorem proved here.
