<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.noiseOperator_firstCoordinateSlice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise on a Coordinate Slice

**Claim.** The noise operator applied to a function on the $(n+1)$-dimensional cube, restricted to first coordinate $b$, equals $b\rho$ times the noise operator on its odd slice plus the noise operator on its even slice.

**Proof.** Compare Fourier coefficients indexed by a subset $S$ of the remaining coordinates; equality of all such coefficients gives equality of the slice functions (`fourier_ext`). The coefficient of the slice at $b$ splits into the coefficient indexed by the tail of $S$ and $\operatorname{sign}(b)$ times the coefficient indexed by that tail with coordinate $0$ inserted (`fourierCoeff_slice_eq_tail_add_sign_mul_insert`). The tail has size $|S|$, and inserting coordinate $0$ increases its size by one, since $0$ is not in the tail (`card_tailFrequency`, `zero_notMem_tailFrequency`). On the proposed right-hand side, the noise operator multiplies the even-part coefficient by $\rho^{|S|}$ and the odd-part coefficient by the same factor, with the additional prefactor $\operatorname{sign}(b)\rho$ on the odd term (`fourierCoeff_noiseOperator`). The even and odd slice coefficient identities identify these coefficients respectively with the original coefficients on the tail and on the tail with $0$ inserted (`fourierCoeff_firstCoordinateEvenPart`, `fourierCoeff_firstCoordinateOddPart`). The two expressions therefore agree: the inserted-coordinate contribution has factor $\operatorname{sign}(b)\rho^{|S|+1}$, as required.

**Key facts.** `FABL.fourier_ext`, `FABL.fourierCoeff_slice_eq_tail_add_sign_mul_insert`, `FABL.card_tailFrequency`, `FABL.zero_notMem_tailFrequency`, `FABL.fourierCoeff_noiseOperator`, `FABL.fourierCoeff_firstCoordinateEvenPart`, `FABL.fourierCoeff_firstCoordinateOddPart`.
