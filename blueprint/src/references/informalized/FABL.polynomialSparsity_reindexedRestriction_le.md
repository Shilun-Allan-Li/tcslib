<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.polynomialSparsity_reindexedRestriction_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparsity under restriction and reindexing

**Claim.** Restricting a function to a coordinate set by fixing all other coordinates, then reindexing the free coordinates by a bijection, cannot increase its number of nonzero Fourier coefficients.

**Proof.** For each frequency $S$ in the restricted function's Fourier support, choose an ambient frequency with nonzero Fourier coefficient whose free-coordinate part is precisely the image of $S$ under the given bijection. Such an ambient frequency exists by the extension lemma for supported restricted frequencies (`exists_ambientFrequency_of_reindexedRestriction_memSupport`). Sending each supported $S$ to this ambient frequency gives a map into the original function's Fourier support, since the chosen coefficient is nonzero (`mem_fourierSupport`). This map is injective: if two chosen ambient frequencies agree, taking their free-coordinate parts recovers the same image of the two original frequencies (`freeFrequencyPart_lift_union`); injectivity of the coordinate bijection then gives equality of those frequencies. Hence the restricted support injects into the original support, so its cardinality is no greater.

**Key facts.** `FABL.exists_ambientFrequency_of_reindexedRestriction_memSupport`, `FABL.mem_fourierSupport`, `FABL.freeFrequencyPart_lift_union`.
