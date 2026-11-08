<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.sum_e3SatSignReplacementClauses -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfying replacement clauses

**Claim.** Among the four sign replacement clauses, the number satisfied by a given input triple is three, with one additional satisfied clause exactly when the product of the input signs equals $b$.

**Proof.** There are four clause indices, corresponding to the four even-parity sign triples. A clause fails precisely when the input agrees with its falsifying triple. In each falsifying triple, the first sign of the corresponding even-parity triple is multiplied by $-b$, so the product of the falsifying triple is $-b$. The four falsifying triples are distinct and exhaust the sign triples whose product is $-b$. Consequently, if the input product is $-b$, exactly one clause fails and three are satisfied; if the input product is $b$, no clause fails and all four are satisfied. Equivalently, the count is three plus one exactly when the input product equals $b$. The proof checks these finite sign possibilities directly.
