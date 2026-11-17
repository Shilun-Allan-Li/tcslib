<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Interpolation.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.nonpos_of_bddAbove_of_half_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonpositivity from bounded half-steps

**Claim.** If the values of a real function on a set are bounded above and every value there is at most half of some other value on the set, then every value on the set is nonpositive.

**Proof.** The image of the set is nonempty because the point under consideration lies in the set. Let $M$ be its supremum. For any value $f(a)$ in the image, the half-step hypothesis gives a point $b$ in the set with $f(a)\le f(b)/2$. Since $f(b)\le M$ and $M$ is an upper bound, it follows that $f(a)\le M/2$. Taking the supremum over all such values yields $M\le M/2$, hence $M\le0$. Every value of the function on the set is at most $M$, so it too is nonpositive.
