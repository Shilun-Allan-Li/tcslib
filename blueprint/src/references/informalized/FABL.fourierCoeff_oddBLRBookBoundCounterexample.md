<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.fourierCoeff_oddBLRBookBoundCounterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd BLR Counterexample Coefficients

**Claim.** For every coordinate set $T$ in the two-dimensional sign cube, the counterexample's Fourier coefficient at $T$ is one half the indicator of $T=\varnothing$, minus one half the indicators that $T$ equals each of $\{0\}$, $\{1\}$, and $\{0,1\}$.

**Proof.** First express the counterexample as $(1-\chi_{\{0\}}-\chi_{\{1\}}-\chi_{\{0,1\}})/2$ (\(\texttt{FABL.oddBLRBookBoundCounterexample_toReal}\)). Multiply by $\chi_T$ and take expectations. Linearity separates the four terms. The expectation of a monomial is $1$ for the empty set and $0$ otherwise (\(\texttt{FABL.expect_monomial}\)); the expectation of the product of two monomials is $1$ when their coordinate sets agree and $0$ otherwise (\(\texttt{FABL.expect_monomial_mul}\)). Applying these identities to the four terms gives exactly the displayed indicators and signs.

**Key facts.** `FABL.oddBLRBookBoundCounterexample_toReal`, `FABL.expect_monomial`, `FABL.expect_monomial_mul`.
