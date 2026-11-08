<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RandomBooleanFourierMaximum.lean :: FABL.finiteUniformEmpiricalMean_randomBooleanCoefficientSampleEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empirical Fourier coefficient

**Claim.** The uniform empirical mean of the sign-valued function obtained from the sample equivalence is the Fourier coefficient at $S$.

**Proof.** Rewrite the Fourier coefficient as the uniform expectation over all inputs, hence as the sum over inputs divided by the number of inputs. The sample equivalence indexes the same Boolean inputs by a finite index set and multiplies each function value by the parity sign on $S$. Reindexing the sum by this equivalence preserves its value. Finally, multiplication of signs becomes multiplication of their real values (`FABL.signValue_mul`), and the real value of the parity sign is the monomial on $S$ (`FABL.signValue_paritySign`). Thus the reindexed average is precisely the Fourier coefficient.

**Key facts.** `FABL.signValue_mul`, `FABL.signValue_paritySign`.
