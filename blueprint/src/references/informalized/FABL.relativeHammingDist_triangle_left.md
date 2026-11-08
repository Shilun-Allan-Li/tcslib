<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.relativeHammingDist_triangle_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triangle Inequality for Relative Hamming Distance

**Claim.** For functions $f,g,h$ on a finite nonempty domain, the relative Hamming distance from $f$ to $g$ is at most the sum of the distances from $h$ to $f$ and from $h$ to $g$.

**Proof.** The unnormalized Hamming distances satisfy $d(f,g)\le d(h,f)+d(h,g)$ (\texttt{hammingDist\_triangle\_left}). Divide this inequality by the positive cardinality of the finite nonempty domain. Since the denominator is positive, division preserves the inequality, and the resulting terms are precisely the three relative Hamming distances in the claim.
