<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.prevSnapSrcs_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of previous-snapshot sources

**Claim.** If $t\,\mathrm{cfgStride}(M,|\ell|,T)\le i$, then every source in the list encoding the previous snapshot at time $t$ is valid for the stated input width, configuration width, and instruction index.

**Proof.** Take a source in the list and unfold its construction as a range-indexed map. Its index $j$ is below the snapshot width. If $t=0$, the source is a constant, hence valid. Otherwise, it is a block source whose block index is the snapshot index at time $t-1$ and whose bit index is $j$. The snapshot index lies before the next stride boundary by `Complexity.snapIdx_lt_succ`; applying `Complexity.prevStep_lt` with the assumed lower bound on $i$ shows that this block index is below $i$. Finally, $j$ is below the snapshot width, hence below the configuration width, which includes the snapshot encoding. These are exactly the two validity conditions for a block source.

**Key facts.** `Complexity.snapIdx_lt_succ`, `Complexity.prevStep_lt`.
