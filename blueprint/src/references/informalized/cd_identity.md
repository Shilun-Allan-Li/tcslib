<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: cd_identity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Christoffel–Darboux Identity for Krawtchouk Polynomials

**Claim.** For the kernel formed from the first $t+1$ Krawtchouk polynomials, there is a positive constant $c$ such that the kernel equals $c$ times the stated antisymmetric product of the degree-$t$ and degree-$(t+1)$ polynomial evaluations, divided by $a-x$.

**Proof.** Set $c=(t+1)/(2\binom{n}{t})$. The conditions on $t$ ensure that both numerator and denominator are positive, so $c>0$. Prove the identity by induction on $t$. At $t=0$, the kernel has just its degree-zero summand; substituting the degree-zero and degree-one Krawtchouk polynomials verifies the formula after clearing the nonzero denominator $a-x$. For the induction step, split the kernel at degree $t+1$ into the kernel through degree $t$ and its final summand. Apply the induction hypothesis to the shorter kernel, then use the defining three-term recurrence for the Krawtchouk polynomials to rewrite the degree-$(t+2)$ term. The relation between consecutive binomial coefficients, $\binom{n}{t+1}=\binom{n}{t}(n-t)/(t+1)$, puts the resulting terms over a common denominator. Since $a\ne x$ and $n-t\ne0$, these denominators can be cleared; the remaining polynomial identity follows by expansion and collection of terms.
