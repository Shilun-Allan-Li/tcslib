<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.depth_parityDepthCircuitFromBlocks -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of the block circuit

**Claim.** For all natural numbers $n,r,q$, the circuit constructed from blocks has depth $q+3$.

**Proof.** By definition, the circuit has depth one plus the layer count of its tail. Its tail is a bottom layer followed by the standard tail with parameter $q$. The bottom layer contributes one layer, and the standard tail has one output layer and one layer for each of the $q$ recursive steps, hence has $q+1$ layers. Therefore the total depth is $1+1+(q+1)=q+3$. The casts used to match layer sizes do not change the tail’s layer count.
