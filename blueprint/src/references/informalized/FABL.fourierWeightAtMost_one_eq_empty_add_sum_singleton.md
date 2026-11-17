<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.fourierWeightAtMost_one_eq_empty_add_sum_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expansion of the Degree-One Fourier Weight

**Claim.** For any real-valued function $f$ on the $n$-dimensional sign cube, its Fourier weight on subsets of size at most one is the square of its empty-set coefficient plus the sum of the squared singleton coefficients.

**Proof.** Index the subsets of size at most one by either no coordinate or one coordinate: these choices are the elements of the option type consisting of `none` and one `some i`. The correspondence sends `none` to the empty set and `some i` to the singleton $\{i\}$. Every subset of size at most one arises uniquely this way, so summing its squared coefficient over those subsets is the same as summing over these options. Splitting that sum into the `none` term and the terms indexed by coordinates gives the empty-set square plus the sum of singleton squares.
