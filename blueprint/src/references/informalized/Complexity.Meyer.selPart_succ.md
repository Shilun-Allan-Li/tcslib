<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.selPart_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Selector Prefixes

**Claim.** Updating the $m$-bit selector prefix at coordinate $m$ to the input bit $y_m$ yields the $(m+1)$-bit selector prefix.

**Proof.** Compare the two functions at an arbitrary selector coordinate $j$. If $j=m$, the update sets the coordinate to $y_m$; the length assumptions ensure this input bit exists. The $(m+1)$-prefix also assigns $y_m$ there. If $j\ne m$, the update leaves the old value unchanged. The cutoff tests $j<m$ and $j<m+1$ then have the same truth value, so both prefix functions return the same old input bit when $j<m$, and false otherwise. Thus the functions agree at every coordinate.
