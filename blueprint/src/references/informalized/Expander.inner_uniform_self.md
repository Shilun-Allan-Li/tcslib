<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Basic.lean :: Expander.inner_uniform_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Norm of the Uniform Vector

**Claim.** The constant vector $u$ with each coordinate equal to $1/n$ satisfies $\langle u,u\rangle=1/n$.

**Proof.** Express the inner product as the sum of coordinatewise products (`inner_eq_sum`). Each of the $n$ summands is $(1/n)^2$, so the sum is $n(1/n)^2=1/n$ when $n\ne0$. When $n=0$, both sides are zero, so the identity holds in that case as well.

**Key facts.** `Expander.inner_eq_sum`.
