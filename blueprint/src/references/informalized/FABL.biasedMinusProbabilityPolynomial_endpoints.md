<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.biasedMinusProbabilityPolynomial_endpoints -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Endpoint values

**Claim.** For a monotone, nonconstant Boolean function, the biased minus-probability polynomial is $0$ at $p=0$ and $1$ at $p=1$.

**Proof.** Monotonicity and nonconstancy imply that $f$ takes the value $1$ at the all-$1$ input and $-1$ at the all-$(-1)$ input (monotone_nonconstant_extreme_values). At bias parameter $1$, the Fourier expansion evaluates the biased expectation polynomial at the all-$1$ input: every monomial there is $1$, so the expansion gives the value of $f$ there. At bias parameter $-1$, each monomial on the all-$(-1)$ input is $(-1)^{|S|}$, so the same expansion gives the value of $f$ at that input. Since the bias mean is $1$ when $p=0$ and $-1$ when $p=1$, substituting these endpoint values into the definition $(1-	ext{biased expectation})/2$ gives $0$ and $1$, respectively.

**Key facts.** `FABL.monotone_nonconstant_extreme_values`, `FABL.fourier_expansion`.
