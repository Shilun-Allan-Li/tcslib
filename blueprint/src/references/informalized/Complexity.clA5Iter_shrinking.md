<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Iter_shrinking -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Iteration of Shrinking Functions

**Claim.** If $f$ and $s$ are polynomial-time computable, the unary encoding of $N$ is polynomial-time computable, and $f$ never increases word length, then $x\mapsto f^{N(x)}(s(x))$ is polynomial-time computable.

**Proof.** Apply the bounded-iteration result with $K=1$. For each fixed input $x$, induction on $j$ shows that $|f^j(s(x))|\le |s(x)|$: it is equality at $j=0$, and the shrinking hypothesis followed by the induction bound proves the successor case. Hence for every $j\le N(x)$ the iterate length is at most $|s(x)|$, which is in turn at most $(|s(x)|+N(x)+1)^2$. This supplies the required quadratic orbit bound, so `clA5Iter_native` gives the conclusion.

**Key facts.** `Complexity.clA5Iter_native`.
