<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.fourierCoeff_slice_eq_tail_add_sign_mul_insert -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of a Coordinate Slice

**Claim.** The Fourier coefficient of the slice with first coordinate fixed to $b$ is the coefficient at the shifted frequency plus the sign value of $b$ times the coefficient at that shifted frequency with the first coordinate added.

**Proof.** The coefficient at the shifted frequency is the average of the coefficients of the two slices fixing the first coordinate to $1$ and $-1$ (`fourierCoeff_tailFrequency`). The coefficient with the first coordinate added is half their difference (`fourierCoeff_insert_zero_tailFrequency`). If $b=1$, adding these two identities gives the coefficient of the $1$-slice; if $b=-1$, subtracting the second identity from the first gives the coefficient of the $-1$-slice. The sign values of $1$ and $-1$ are respectively $1$ and $-1$ (`signValue_one`, `signValue_neg_one`), so these two cases give the claimed formula.

**Key facts.** `FABL.fourierCoeff_tailFrequency`, `FABL.fourierCoeff_insert_zero_tailFrequency`, `FABL.signValue_one`, `FABL.signValue_neg_one`.
