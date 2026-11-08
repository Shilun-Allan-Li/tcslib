<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticTruncation_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Quadratic Truncations

**Claim.** The truncation retaining the first $k+1$ coordinates is the truncation retaining the first $k$ coordinates plus the vector supported at coordinate $k$ with value equal to the image of $w_k$.

**Proof.** Compare the two sides at an arbitrary coordinate $i$. If $i<k$, both truncations retain the mapped value of $w_i$, and the added single-coordinate vector vanishes there. If $i=k$, the shorter truncation is zero at that coordinate, while the added vector supplies the mapped value of $w_k$, which is also what the longer truncation retains. Finally, if $i\not<k$ and $i\ne k$, then $i>k$: both truncations vanish there, and the single-coordinate vector does too. These cases establish coordinatewise equality.
