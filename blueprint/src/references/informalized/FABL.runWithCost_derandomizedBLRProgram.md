<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.runWithCost_derandomizedBLRProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full derandomized BLR outcome law

**Claim.** The derandomized BLR program has the law obtained by choosing independent uniform input and seed bit vectors, returning the corresponding BLR decision, and assigning cost $(0,3,n+r+(2n+1)+3)$.

**Proof.** Expand the program’s outer bind. The first random bit vector program chooses a uniform input vector and contributes cost $(0,0,n)$; the random-bit-vector cost law gives this distribution (`runWithCost_randomBitVectorProgram`). For each input vector, the after-input program chooses uniform seed bits and returns the BLR decision with cost $(0,3,r+(2n+1)+3)$, by its outcome law (`runWithCost_derandomizedBLRAfterInputProgram`). Combining the two stages adds their costs, yielding $(0,3,n+r+(2n+1)+3)$; the equality of cost triples is justified componentwise, using injectivity of the triple representation (`LearningCost.toTriple_injective`). The probability bind and map identities combine the two uniform choices into the joint law of an input vector and seed vector. This is the uniform law on their product, by the product-uniformity identity (`uniformPMF_bind_map_pair`).

**Key facts.** `FABL.LearningCost.toTriple_injective`, `FABL.LearningProgram.runWithCost_bind`, `FABL.runWithCost_randomBitVectorProgram`, `FABL.runWithCost_derandomizedBLRAfterInputProgram`, `FABL.uniformPMF_bind_map_pair`.
