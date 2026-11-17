<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.pmfExpectation_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Difference

**Claim.** The expectation of the pointwise difference of two functions is the difference of their expectations.

**Proof.** Expand each expectation as a finite sum. Distribute the difference across the sum, then use $(p(x))_{\mathbb R}(f(x)-g(x))=(p(x))_{\mathbb R}f(x)-(p(x))_{\mathbb R}g(x)$ term by term. The resulting sums are precisely the expectations of $f$ and $g$, whose difference is the required expression.
