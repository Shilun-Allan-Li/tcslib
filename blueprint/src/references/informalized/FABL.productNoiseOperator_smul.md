<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productNoiseOperator_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar Linearity of Product Noise

**Claim.** For every real scalar $c$ and function $f$, applying the product noise operator to $cf$ gives $c$ times its application to $f$.

**Proof.** Evaluate at an arbitrary input $x$. The operator takes expectation under the noise kernel at $x$, and the expectation of a constant multiple is that constant times the expectation (FABL.pmfExpectation_const_mul). Thus the two functions agree at every input.

**Key facts.** `FABL.pmfExpectation_const_mul`.
