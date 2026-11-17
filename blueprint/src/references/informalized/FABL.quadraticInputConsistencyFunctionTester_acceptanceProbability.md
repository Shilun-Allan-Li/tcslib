<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticInputConsistencyFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability under proof reindexing

**Claim.** For positive $n$, the quadratic input consistency tester's acceptance probability on $(w,p)$ equals that of the affine consistency tester on $(w,q)$, where $q$ is obtained by reading the first $2^n$ entries of $p$ at their designated indices.

**Proof.** The quadratic tester is formed by padding the affine tester with a fourth, unused query slot and reindexing its query addresses into the larger proof domain. Padding preserves acceptance probability (\texttt{padThreeQueryFunctionTester_acceptanceProbability}), and reindexing the domain changes the oracle seen by the original tester to its composition with the address map (\texttt{reindexDomainFunctionTester_acceptanceProbability}). It remains to identify that composed oracle. On an input address it returns $w(i)$ unchanged. On a proof-table address $j$, the reindexing reads $p$ at the designated linear-proof index; by definition this is exactly $q(j)$. Hence the two testers have the same acceptance probability.

**Key facts.** `FABL.padThreeQueryFunctionTester_acceptanceProbability`, `FABL.reindexDomainFunctionTester_acceptanceProbability`.
