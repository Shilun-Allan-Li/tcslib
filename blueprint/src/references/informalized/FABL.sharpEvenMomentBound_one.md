<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.sharpEvenMomentBound_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First sharp even-moment bound

**Claim.** For every positive natural number $r$, the sharp even-moment bound at index $1$ equals $1$.

**Proof.** At index $1$, the defining expression has numerator $(2r-1)\binom{r}{1}$ and denominator $\binom{2r}{2}$. The binomial identities $\binom{r}{1}=r$ and $\binom{2r}{2}=r(2r-1)$ reduce the expression to $r(2r-1)/(r(2r-1))$. Positivity of $r$ ensures both factors are nonzero, so the quotient is $1$.
