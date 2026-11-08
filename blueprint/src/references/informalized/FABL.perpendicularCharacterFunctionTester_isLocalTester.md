<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.perpendicularCharacterFunctionTester_isLocalTester -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perpendicular Character Tester

**Claim.** The three-query tester associated with a coordinate decomposition having $H$ as its first factor is a local tester of rate $1$ for the perpendicular characters: it accepts each such character with probability $1$, and any sign-valued function more than $\epsilon$ away from every character is rejected with probability greater than $\epsilon$.

**Proof.** Apply the general theorem for a tester built from a binary subspace split: it says that for any such split, the associated three-query tester is a local tester of rate $1$ for the perpendicular characters (\texttt{splitCharacterFunctionTester_isLocalTester}). Instantiate that result with the split obtained from $H$. This gives exactly the claimed completeness and soundness properties for the tester in the statement.

**Key facts.** `FABL.splitCharacterFunctionTester_isLocalTester`.
