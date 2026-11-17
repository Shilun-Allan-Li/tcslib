<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DegreeOneWeight.lean :: FABL.sum_sq_vectorFourierCoeff_support_card_one_setIndicator_coordinateSubcube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Weight of a Coordinate Subcube

**Claim.** For the indicator of the coordinate subcube determined by a set of coordinates and a base point, the sum of squared vector Fourier coefficients over vectors with support of size one is the number of fixed coordinates times the square of the subcube density.

**Proof.** Vectors whose support has size one are in bijection with the individual coordinates: the vector associated to $i$ is the one whose support is $\{i\}$. Thus the stated sum is the sum, over all coordinates $i$, of the squared coefficient at that singleton support. For each such vector, the absolute-value formula for the Fourier coefficient of a coordinate-subcube indicator (`FABL.abs_vectorFourierCoeff_setIndicator_coordinateSubcube`) says its magnitude is $(2^{|C|})^{-1}$ if $i$ belongs to the fixed-coordinate set $C$, and zero otherwise. Squaring removes any sign, so precisely the $|C|$ coordinates in $C$ contribute, each by $(2^{|C|})^{-2}$. The total is $|C|(2^{|C|})^{-2}$, as claimed.

**Key facts.** `FABL.abs_vectorFourierCoeff_setIndicator_coordinateSubcube`.
