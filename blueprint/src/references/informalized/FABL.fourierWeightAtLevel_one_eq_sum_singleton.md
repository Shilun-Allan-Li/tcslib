<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.fourierWeightAtLevel_one_eq_sum_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-one Fourier weight

**Claim.** The level-one Fourier weight of a function on the Boolean cube is the sum of the squares of its singleton Fourier coefficients.

**Proof.** The level-one weight sums squared coefficients over subsets whose cardinality is one. Every such subset is uniquely a singleton $\{i\}$, and every coordinate gives one such subset. Reindexing the finite sum by this bijection gives $\sum_i\widehat f(\{i\})^2$.
