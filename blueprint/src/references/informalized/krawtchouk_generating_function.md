<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: krawtchouk_generating_function -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Krawtchouk generating function

**Claim.** For $x\le n$, the generating sum of the Krawtchouk polynomials equals $(1-z)^x(1+z)^{n-x}$.

**Proof.** Expand the defining coefficient as a sum over $i$, then interchange the finite sums over the degree $j$ and index $i$. Terms with $i>x$ vanish, leaving $0\le i\le x$. For each fixed $i$, write $j=i+h$; the inner sum over $h$ is $z^i(1+z)^{n-x}$ by the binomial theorem. The remaining sum over $i$ is $\sum_{i=0}^{x}(-1)^i\binom{x}{i}z^i=(1-z)^x$, again by the binomial theorem. Multiplying these two factors gives the claimed identity.
