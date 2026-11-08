<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.expect_majorityThreeParity_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority parity expectation identity

**Claim.** For independent uniform $a,b,c$ in a finite set, the expected product of the three-variable majority parity expression with $P(a)P(b)P(c)$ is $-\frac12(\mathbb E[F(a)P(a)])^3$, provided $P$ has mean zero.

**Proof.** Distribute the product to write the integrand as the sum of three terms, each containing one factor $F$ paired with its corresponding $P$, minus the term containing all three factors $F(a)P(a)$, $F(b)P(b)$, and $F(c)P(c)$; each term has the common factor $1/2$. Independence factors each triple expectation into the product of its one-coordinate expectations (`FABL.expect_triple_mul_separate`). In each of the first three terms, two factors are the mean of $P$, so those terms vanish. The remaining term is $-\frac12$ times the cube of the mean of $FP$. Pulling the constant $1/2$ through the expectation gives the stated identity (`FABL.expect_div_const`).

**Key facts.** `FABL.expect_triple_mul_separate`, `FABL.expect_div_const`.
