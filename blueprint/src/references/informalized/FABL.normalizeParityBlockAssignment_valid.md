<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.normalizeParityBlockAssignment_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity After Normalization

**Claim.** After normalization, the assignment has value $1$ at every index $j$ for which $n\le gr+j$.

**Proof.** Fix such an index $j$. The inequality implies that $gr+j<n$ is false. The normalization rule therefore assigns the value $1$ at $j$, as required.
