<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.lovasz_test_int -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integer-Valued Determinant Test

**Claim.** If $A$ has a perfect matching, $2n\le 2^k$, and $n^2k\le m$, then the integer-valued randomized determinant test accepts with probability at least $1/2$.

**Proof.** Apply the general randomized determinant bound (`lovasz_test`) with coefficient ring $\mathbb Z$. The size hypotheses are exactly those required by that bound. The required injectivity of the natural-number embedding on the range of $2^k$ follows from injectivity of the map $a\mapsto\operatorname{Int.ofNat}(a)$: equal integer casts imply equal natural numbers. The general bound then gives the claimed probability estimate.

**Key facts.** `Randomized.Matching.lovasz_test`.
