<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.runWithCost_derandomizedBLRAfterInputProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeded BLR outcome and cost

**Claim.** For a fixed input bit vector, the program’s outcome and cost have the law obtained by choosing a uniform seed, returning the BLR decision for the corresponding cube points, and assigning cost $(0,3,r+(2n+1)+3)$.

**Proof.** Expand the program’s outer bind: first it runs the random bit vector program to obtain the seed bits, then runs the ticked three-query test determined by those bits. The random bit vector program’s outcome law is uniform on the seed vectors, with cost $(0,0,r)$ ( `runWithCost_randomBitVectorProgram`). For each such seed, the ticked query test returns the BLR decision with cost $(0,3,2n+1+3)$, by the cost law for that test (`runWithCost_derandomizedBLRTickQueryProgram`). Binding these laws adds their costs while preserving the output, so the seed contribution and test contribution give $(0,3,r+(2n+1)+3)$. The bind and map identities for probability mass functions then express the result as the uniform seed law mapped to that decision and fixed cost.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.runWithCost_randomBitVectorProgram`, `FABL.runWithCost_derandomizedBLRTickQueryProgram`.
