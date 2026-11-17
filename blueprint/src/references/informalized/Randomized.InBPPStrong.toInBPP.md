<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.InBPPStrong.toInBPP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strong randomized verification implies BPP

**Claim.** A verifier with correctness probabilities at least $1-2^{-((|x|+1)^d+1)}$ on the appropriate inputs also has both correctness probabilities at least $2/3$.

**Proof.** Unpack the strong verifier and retain its machine and polynomial random-bit bound. For an input $x$, the exponent $(|x|+1)^d+1$ is at least $2$, since $|x|+1\ge 1$. As $1/2$ lies between zero and one, increasing the exponent decreases its power, so $2^{-((|x|+1)^d+1)}\le 1/4$. Hence the strong lower bound is at least $1-1/4=3/4$, and therefore at least $2/3$. This numerical bound applies uniformly to both the acceptance condition for members and the rejection condition for nonmembers; composing it with the respective strong guarantees proves the required BPP bounds.
