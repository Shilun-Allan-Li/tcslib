<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Pack_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound for Packed Records

**Claim.** There is a polynomially bounded function of the input length that bounds the length of every packed record word whose cursor is at most one beyond the last round.

**Proof.** By the packed-record machine and length bound (`clPackedRecords_machine`), choose constants $a,r$ such that the packed record word for $x$ has length at most $a(|x|+1)^r$. Let $R(n)$ be the last-round bound at input length $n$. The fuel estimate (`clA5Fuel`) says that $R$ is polynomially bounded. The packed word prepends a pair encoding of a unary word of length $i$ and the packed records. Its length is therefore $2i+|\mathrm{clPackedRecords}(x)|+2$. When $i\le R(|x|)+1$, this is at most $2(R(|x|)+1)+a(|x|+1)^r+2$. The displayed bound is polynomially bounded: the polynomial-call estimate (`clA5Poly_call`) handles the scaled fuel term, and closure under sums (`clA5Poly_add`) combines it with the packed-record polynomial and the constant term.

**Key facts.** `Complexity.clPackedRecords_machine`, `Complexity.clA5Fuel`, `Complexity.clA5Poly_call`, `Complexity.clA5Poly_add`.
