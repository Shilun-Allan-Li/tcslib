<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LimitingMajorityWeights.lean :: FABL.limitingMajorityFourierWeightAbove_summable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summability of the majority weights

**Claim.** For every natural number $k$, the limiting majority Fourier weights indexed by $j>k$ form a summable series.

**Proof.** The full sequence of limiting majority Fourier weights has sum one, so it is summable (FABL.limitingMajorityFourierWeight_hasSum_one). Restricting a summable sequence to the subset of indices $j>k$ preserves summability; hence the indicated tail series is summable.

**Key facts.** `FABL.limitingMajorityFourierWeight_hasSum_one`.
