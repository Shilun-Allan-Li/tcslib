<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductSmallBiasRandomBits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random-bit count bound

**Claim.** For every natural number $n$, the specified number of random bits is at most four times $\lceil\log_2(n+1)\rceil+1$.

**Proof.** The random-bit count is the sum of two copies of the degree. By the degree bound (\texttt{FABL.matrixProductSmallBiasDegree_le}), each copy is at most $2+\lceil\log_2(n+1)\rceil$. Adding these bounds gives $4+2\lceil\log_2(n+1)\rceil$, which is at most $4(1+\lceil\log_2(n+1)\rceil)$ by elementary arithmetic.

**Key facts.** `FABL.matrixProductSmallBiasDegree_le`.
