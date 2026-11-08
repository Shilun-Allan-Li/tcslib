<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.measure_finiteFamily_someCoefficient_bad_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-tenth coefficient failure bound

**Claim.** For a nonempty finite family and the specified accuracy parameter, the probability that at least one empirical Fourier coefficient is bad is at most $1/10$.

**Proof.** Use the one-tenth bound for the parameterized bad sets (`FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le_one_tenth`) with the finite-family accuracy parameter. The definitions of the sample count and bad sets then identify this event with the union in the claim, yielding the stated bound.

**Key facts.** `FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le_one_tenth`.
