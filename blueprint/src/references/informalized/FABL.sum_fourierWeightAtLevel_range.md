<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierFormulas.lean :: FABL.sum_fourierWeightAtLevel_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Fourier Weight by Levels

**Claim.** The sum of the Fourier weights over levels $0$ through $n$ equals the sum of the squared Fourier coefficients over all subsets of the coordinate set.

**Proof.** For each level $k$, its Fourier weight is the sum of the squared coefficients over sets of cardinality $k$. Summing these expressions over $k=0,\ldots,n$ groups every subset exactly once: every subset of the $n$-element coordinate set has cardinality at most $n$, and its cardinality determines its unique level. Reindexing the finite sum by this partition gives the sum over all subsets.
