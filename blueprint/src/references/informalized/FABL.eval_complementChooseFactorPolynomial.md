<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.eval_complementChooseFactorPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary Binomial Evaluation

**Claim.** For natural numbers $n,z,k$ with $z\le n$, evaluating the complementary falling-factorial polynomial at $z$ gives $\binom{n-z}{k}$.

**Proof.** Evaluate the product after substitution by applying the evaluation rules for products, constants, composition, subtraction, and the indeterminate. The substituted falling factorial becomes the falling factorial of $n-z$. The hypothesis $z\le n$ justifies rewriting the cast of $n-z$ as the difference of the real casts of $n$ and $z$. The falling-factorial formula for binomial coefficients then identifies the result as $\binom{n-z}{k}$; rearranging the factorial denominator and product is ordinary algebra.
