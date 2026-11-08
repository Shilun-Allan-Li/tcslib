<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluence_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coalitional Influence Bounds

**Claim.** For every Boolean function $f$ and coordinate set $J$, the coalitional influence lies in $[0,1]$.

**Proof.** On each input, the indicator of the event that both signs are attainable is either zero or one. Thus its sum over the finite sign cube is nonnegative and is at most the sum of the constant function one. Dividing by the positive cardinality of the cube expresses the uniform average and preserves these bounds, giving a value in $[0,1]$.
