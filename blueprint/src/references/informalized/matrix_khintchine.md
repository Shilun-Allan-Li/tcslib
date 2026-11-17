<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/KikuchiLDC/LDC/BackgroundFacts.lean :: matrix_khintchine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive square-root witness

**Claim.** Under the stated positivity hypotheses, there exists a positive real number no greater than $\sqrt{2\sigma^2\log(d_1+d_2)}$.

**Proof.** Take the witness to be $C_{\mathrm{MK}}=\sqrt{2\sigma^2\log(d_1+d_2)}$. Since $\sigma^2>0$ and $d_1+d_2\ge2$, both factors inside the square root are positive, so the square root is positive. It is equal to the stated upper bound, and therefore is no greater than that bound.

**Caveat.** The formal statement only asserts the existence of a positive scalar bounded above by this expression; it does not assert the matrix Gaussian and Rademacher series estimates in the supplied informal discussion.
