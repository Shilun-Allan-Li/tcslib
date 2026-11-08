<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.two_mul_lt_of_odd_of_two_mul_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict bound from oddness

**Claim.** If $n$ and $k$ are natural numbers, $n$ is odd, $k>0$, and $2k^2\le n$, then $2k<n$.

**Proof.** Because $k>0$, we have $1\le k$, hence $k=k\cdot1\le k\cdot k=k^2$. Multiplying by $2$ and using the assumed bound gives $2k\le n$. Equality would make $n=2k$ even, contradicting that $n$ is odd. Thus the inequality is strict.
