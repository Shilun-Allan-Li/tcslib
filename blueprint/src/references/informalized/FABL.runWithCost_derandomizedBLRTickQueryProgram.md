<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.runWithCost_derandomizedBLRTickQueryProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of the ticked BLR test

**Claim.** For fixed cube points $x,y$, the ticked three-query BLR test returns the BLR decision and has cost $(0,3,2n+1+3)$.

**Proof.** The three-query test has a deterministic outcome equal to the BLR decision and cost $(0,3,3)$ (`runWithCost_derandomizedBLRQueryProgram`). The tick adds $2n+1$ units of local work and leaves the output and query count unchanged. Adding the cost triples gives $(0,3,2n+1+3)$; equality of the cost structures follows from injectivity of their triple representation (`LearningCost.toTriple_injective`).

**Key facts.** `FABL.LearningCost.toTriple_injective`, `FABL.runWithCost_derandomizedBLRQueryProgram`.
