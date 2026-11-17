<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productNoiseOperator_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of the Product Noise Operator

**Claim.** For real-valued functions $f,g$ on $\Omega^n$, applying the product noise operator to $f+g$ gives the sum of its applications to $f$ and $g$.

**Proof.** Evaluate both sides at an arbitrary input $x$. The noise operator there is expectation with respect to the same noise kernel. Expectation is additive (FABL.pmfExpectation_add), so the value on $f+g$ is the sum of the values on $f$ and $g$. Since this holds at every input, the functions are equal.

**Key facts.** `FABL.pmfExpectation_add`.
