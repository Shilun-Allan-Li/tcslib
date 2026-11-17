<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.eq_of_relativeHammingDist_eq_zero_amplification -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero relative Hamming distance implies equality

**Claim.** For functions on a finite nonempty domain, zero relative Hamming distance implies that the functions are equal.

**Proof.** By definition, the relative Hamming distance is the Hamming distance divided by the domain’s cardinality. The domain is nonempty, so that cardinality is positive and hence nonzero as a real number. A zero quotient with nonzero denominator forces the Hamming distance, viewed as a real number, to be zero; therefore the natural-number Hamming distance itself is zero. Hamming distance is zero exactly when the two functions agree at every input, so f=g.
