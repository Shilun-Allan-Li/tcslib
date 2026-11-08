<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.size_parityDepthCircuitFromBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Layer sizes of the block circuit

**Claim.** For the circuit built from blocks, its size is the sum of the layer sizes $r^k2^r$ for $0\le k<q+2$.

**Proof.** The circuit size is the number of gates in its first layer plus the number of internal nodes in its tail. The first layer contributes the layer size for index $q+1$. The padded tail contributes the bottom layer at index $q$, followed by the standard tail whose remaining layers have indices $0$ through $q-1$. Thus the total is the sum of the layer sizes from $0$ through $q+1$, as claimed.
