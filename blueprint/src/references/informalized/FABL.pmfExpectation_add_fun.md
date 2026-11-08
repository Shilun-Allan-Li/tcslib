<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.pmfExpectation_add_fun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Expectation

**Claim.** For a probability mass function on a finite set, the expectation of the pointwise sum of two real-valued functions is the sum of their expectations.

**Proof.** The expectation is a finite sum of the function values weighted by the corresponding probabilities. Applying the finite-sum additivity formula for expectation to the pointwise sum gives the sum of the two expectations (\texttt{FABL.pmfExpectation\_add}).

**Key facts.** `FABL.pmfExpectation_add`.
