<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.productInner_sq_le_secondMoment_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cauchy–Schwarz for Product Inner Products

**Claim.** The square of the product inner product of $f$ and $g$ is at most the product of their second moments under the independent product distribution.

**Proof.** For each input $x$, let $w(x)$ be the square root of its probability under the product distribution. This is real because every probability weight is nonnegative. The product inner product is then the finite sum of $(w(x)f(x))(w(x)g(x))$, while the second moments are respectively the sums of $(w(x)f(x))^2$ and $(w(x)g(x))^2$. Cauchy–Schwarz for finite sums gives the desired inequality.
