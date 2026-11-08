<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.two_pow_bits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on the Binary Digit Length

**Claim.** For every nonnegative integer $n$, $2^{\ell(n)}\le2n+1$, where $\ell(n)$ is the length of the binary expansion of $n$, taken to be zero when $n=0$.

**Proof.** The length of the binary expansion equals the binary size of $n$. If $n=0$, the inequality is immediate. Otherwise the size is positive. The defining property of binary size gives $n<2^{\mathrm{size}(n)}$, and the exponent identity $2^{s}=2\cdot2^{s-1}$ for positive $s$ then yields $2^{\mathrm{size}(n)}<2n+2$. Since both sides are integers, this implies $2^{\mathrm{size}(n)}\le2n+1$, proving the claim.
