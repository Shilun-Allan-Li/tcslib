<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.runWithCost_derandomizedBLRProgram_eq_pure_of_isF₂Linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance for a linear target

**Claim.** If the binary encoding of the target is additive, then the derandomized BLR program returns true for every input and seed, so its outcome-cost law is the point mass at true with cost $(0,3,n+r+(2n+1)+3)$.

**Proof.** Use the full outcome law for the derandomized BLR program (`runWithCost_derandomizedBLRProgram`). For every pair of input and seed bit vectors, additivity of the encoded target says its value at the sum of the two corresponding cube points equals the sum of its values at those points. Thus the BLR equality holds, and the decision is true for every pair. The map in the outcome law is therefore constant, always returning true with the fixed cost. Mapping a probability law by a constant function gives the point mass at that value, proving the claim.

**Key facts.** `FABL.runWithCost_derandomizedBLRProgram`.
