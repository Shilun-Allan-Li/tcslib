<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPPAmplify.lean :: Randomized.BPP_PTMWith_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Acceptance Threshold

**Claim.** If the threshold function $q$ is everywhere at most $p$, every language decidable in polynomial time with correctness probability at least $p(n)$ is also decidable in polynomial time with correctness probability at least $q(n)$.

**Proof.** Take a language in the class with threshold $p$. Unpacking the union defining the class supplies an exponent, a time constant, and a randomized machine that halts within the prescribed polynomial time and achieves probability at least $p(|x|)$ on each input $x$. Keep the same exponent, constant, and machine. For every input, the assumed inequality $q(|x|)\le p(|x|)$ followed by the machine's probability guarantee gives the required lower bound $q(|x|)$. The halting-time guarantee is unchanged, so the language belongs to the class with threshold $q$.
