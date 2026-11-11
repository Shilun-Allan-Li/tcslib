<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticSystemProofFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability Reindexing

**Claim.** The four-query proof tester’s acceptance probability on the combined word formed from $w$ and $p$ equals the three-query character tester’s acceptance probability on the matrix function obtained by reading $p$ at the flattened-matrix proof-table positions.

**Proof.** The proof tester is defined by padding the three-query tester, converting its answers from Boolean values to $\mathbb F_2$, and reindexing matrix-cube queries as proof-word addresses. Padding preserves acceptance probability because its extra slot is unused, and Boolean-to-$\mathbb F_2$ conversion preserves it by interpreting each queried Boolean answer through the fixed alphabet equivalence (`padThreeQueryFunctionTester_acceptanceProbability`, `boolFunctionTesterOfF₂_acceptanceProbability`). Reindexing the domain then identifies the input function seen by the underlying tester as the original input composed with the matrix-cube address map (`reindexDomainFunctionTester_acceptanceProbability`). At each cube point, that address lies in the proof-table portion of the combined word; expanding the definitions of the combined word, proof table, and matrix proof function shows that the resulting value is exactly the stated matrix function. Thus the two acceptance probabilities agree.

**Key facts.** `FABL.padThreeQueryFunctionTester_acceptanceProbability`, `FABL.boolFunctionTesterOfF₂_acceptanceProbability`, `FABL.reindexDomainFunctionTester_acceptanceProbability`.
