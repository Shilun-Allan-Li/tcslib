<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.fourierDegree_linearForm_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a linear form

**Claim.** For every real coefficient vector $a$, the linear form $x\mapsto\sum_i a_i x_i$ on the Boolean cube has Fourier degree at most $1$.

**Proof.** By the degree criterion (`fourierDegree_le_iff`), consider a frequency set $S$ with $|S|>1$. Expand its Fourier coefficient as a sum over coordinates $i$, with each summand a scalar multiple of the expected product of the singleton monomial at $i$ and the monomial indexed by $S$. The product of two cube monomials has expectation zero unless their index sets agree (`expect_monomial_mul`). Here they cannot agree: a singleton has size one, whereas $|S|>1$. Every summand is therefore zero, so the coefficient at $S$ vanishes. This proves the degree bound.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.expect_monomial_mul`.
