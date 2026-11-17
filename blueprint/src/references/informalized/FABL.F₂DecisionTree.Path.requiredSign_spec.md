<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.F₂DecisionTree.Path.requiredSign_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Required sign of an assigned bit

**Claim.** At a supported coordinate assigned the bit $b$, the required sign is the sign encoding of $b$.

**Proof.** The required sign is defined by applying the sign encoding to the value stored in the assignment at the coordinate. Under the hypothesis that this assignment equals `some b`, extracting the value from that option returns $b$. Thus the required sign is `signEncode b`, as claimed.
