<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.pmfExpectation_point_indicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Point Indicator

**Claim.** The expectation under $p$ of the function equal to one at $a$ and zero elsewhere is the mass $p(a)$.

**Proof.** The point-indicator identity (`indicatorPolynomial_eq_ite`) identifies the function with $1$ when the input is $a$ and $0$ otherwise. In the finite sum defining expectation, every term except the one indexed by $a$ therefore vanishes; the remaining term is $(p(a)).\mathrm{toReal}$.

**Key facts.** `FABL.indicatorPolynomial_eq_ite`.
