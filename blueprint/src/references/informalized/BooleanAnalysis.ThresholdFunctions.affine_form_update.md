<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.affine_form_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Separation in an Affine Form

**Claim.** For the stated $c,a,i,x,b$, the affine form after replacing coordinate $i$ of $x$ by $b$ is the sum of the contribution from the other coordinates and the contribution $a_i\sigma(b)$ from coordinate $i$.

**Proof.** Split the sum over coordinates into the term at $i$ and the sum over all other coordinates. For every $j\ne i$, updating coordinate $i$ leaves $x_j$ unchanged, so those summands are $a_j\sigma(x_j)$. At coordinate $i$, the updated value is $b$, giving the term $a_i\sigma(b)$. Reassembling these terms gives the asserted identity.
