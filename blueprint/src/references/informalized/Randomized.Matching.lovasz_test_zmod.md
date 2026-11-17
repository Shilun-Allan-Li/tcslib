<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/MatchingMath.lean :: Randomized.Matching.lovasz_test_zmod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Field Determinant Test

**Claim.** Under the stated prime-field size and bit-length assumptions, the randomized determinant test over $\mathbb Z/p\mathbb Z$ accepts with probability at least $1/2$.

**Proof.** Use the general randomized determinant bound (`lovasz_test`) for $R=\mathbb Z/p\mathbb Z$. It remains to check that natural numbers below $2^k$ have distinct residues modulo $p$. Such numbers are strictly less than $p$, since $2^k\le p$. If two of them have equal residues, the characterization of equality of natural casts in $\mathbb Z/p\mathbb Z$ says they are congruent modulo $p$; because both are below $p$, reducing each modulo $p$ leaves it unchanged, so the numbers are equal. This supplies the injectivity hypothesis, and the general bound yields the result.

**Key facts.** `Randomized.Matching.lovasz_test`.
