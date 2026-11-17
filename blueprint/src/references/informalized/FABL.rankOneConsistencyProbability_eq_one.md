<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.rankOneConsistencyProbability_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rank-One Matrix Consistency

**Claim.** For any $n$ and $\gamma\in\mathbb F_2^n$, independent uniform vectors $x,y\in\mathbb F_2^n$ satisfy $(\gamma\cdot x)(\gamma\cdot y)=\sum_{i,j}\gamma_i\gamma_jx_i y_j$ with probability $1$.

**Proof.** For the rank-one matrix with entries $\gamma_i\gamma_j$, its pairing with $x,y$ equals $(\gamma\cdot x)(\gamma\cdot y)$ (\texttt{matrixRankOnePairing\_rankOneSelfMatrix}). Thus the consistency condition holds for every pair $(x,y)$, so the indicator of that condition is constantly $1$. The uniform expectation of a constant $1$ is $1$, proving that the probability is $1$.

**Key facts.** `FABL.matrixRankOnePairing_rankOneSelfMatrix`.
