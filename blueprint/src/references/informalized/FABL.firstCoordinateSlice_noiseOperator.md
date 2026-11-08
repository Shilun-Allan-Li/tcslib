<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.firstCoordinateSlice_noiseOperator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-Coordinate Slice of the Noise Operator

**Claim.** The first-coordinate slice at $b$ of the noise operator applied to $f$ is the sum of $\operatorname{signValue}(b)\rho$ times the noise operator applied to the odd part of $f$, and the noise operator applied to the even part of $f$.

**Proof.** It is enough to compare Fourier coefficients, since equality of all Fourier coefficients determines a function on the sign cube (\texttt{smallSet\_fourier\_ext}). Fix a tail frequency $S$. The coefficient of the sliced noise operator is the sum of the coefficients of $f$ at the tail frequency and at the frequency obtained by adjoining the first coordinate, with the latter multiplied by $\operatorname{signValue}(b)$ (\texttt{fourierCoeff\_slice\_tail\_add\_insert}). Applying the noise operator multiplies a coefficient at frequency $T$ by $\rho^{|T|}$ (\texttt{fourierCoeff\_noiseOperator}). The tail frequency has size $|S|$, while adjoining the first coordinate increases its size to $|S|+1$; the first coordinate is absent from every tail frequency (\texttt{zero\_notMem\_tailFrequency}), and tail frequencies preserve cardinality (\texttt{card\_tailFrequency}). On the other side, the Fourier coefficients of the even and odd parts are respectively those of $f$ at the tail frequency and at the frequency with the first coordinate adjoined (\texttt{fourierCoeff\_hypercontractiveEvenPart}, \texttt{fourierCoeff\_hypercontractiveOddPart}). After the noise multipliers are applied, the coefficients on both sides agree: the even contribution has factor $\rho^{|S|}$, and the odd contribution has factor $\operatorname{signValue}(b)\rho^{|S|+1}$. Thus all Fourier coefficients agree, proving the function identity.

**Key facts.** `FABL.smallSet_fourier_ext`, `FABL.fourierCoeff_slice_tail_add_insert`, `FABL.fourierCoeff_noiseOperator`, `FABL.card_tailFrequency`, `FABL.zero_notMem_tailFrequency`, `FABL.fourierCoeff_hypercontractiveEvenPart`, `FABL.fourierCoeff_hypercontractiveOddPart`.
