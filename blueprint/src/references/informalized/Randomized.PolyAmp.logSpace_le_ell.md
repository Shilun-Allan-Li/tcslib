<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.logSpace_le_ell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Length Comparison

**Claim.** For every natural number $n$, $\lfloor\log_2 n\rfloor+1$ is at most one more than the length of the binary representation of $n$.

**Proof.** If $n=0$, both quantities reduce to $1$, so the inequality holds. If $n>0$, `lt_two_pow_bits` gives $n<2^{|\operatorname{bits}(n)|}$. The logarithm bound for a number strictly below a power of the base $2$ then yields $\lfloor\log_2 n\rfloor<|\operatorname{bits}(n)|$. Adding one gives $\logSpace(n)=\lfloor\log_2 n\rfloor+1\le |\operatorname{bits}(n)|+1=\ell(n)$.

**Key facts.** `Randomized.PolyAmp.lt_two_pow_bits`.
