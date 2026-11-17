<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/BitFlipSets.lean :: BooleanAnalysis.ThresholdFunctions.mem_fiber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a Color Class

**Claim.** For a map $\pi:\{0,\ldots,n-1\}\to\{0,\ldots,m-1\}$ and indices $i,j$ in the respective sets, $i$ belongs to the color class of $j$ exactly when $\pi(i)=j$.

**Proof.** The color class of $j$ consists of precisely those indices in the full index set that the map sends to $j$. Thus membership in the filtered set is equivalent to the defining condition $\pi(i)=j$.
