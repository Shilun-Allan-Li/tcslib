<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.isBent_iff_distanceToAffineSigns_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bentness and affine-sign distance

**Claim.** For even $n$ and a sign-valued real function on the binary cube, bentness is equivalent to its minimum relative Hamming distance from affine sign functions being $\frac12-\frac12(2^{n/2})^{-1}$.

**Proof.** Assume first that $f$ is bent. Its spectral infinity norm is then $(2^{n/2})^{-1}$ (`IsBent.spectralInfinityNorm_eq`). The distance formula for sign-valued functions expresses the minimum relative Hamming distance as $\frac12$ minus half the spectral infinity norm (`distanceToAffineSigns_eq`), giving the claimed value. Conversely, suppose the distance has the claimed value. Substituting the same distance formula and rearranging yields spectral infinity norm $(2^{n/2})^{-1}$. For even dimension and sign-valued $f$, that spectral norm forces every Fourier coefficient to have absolute value $(2^{n/2})^{-1}$ (`isBent_of_spectralInfinityNorm_eq`), which is precisely bentness.

**Key facts.** `FABL.IsBent.spectralInfinityNorm_eq`, `FABL.distanceToAffineSigns_eq`, `FABL.isBent_of_spectralInfinityNorm_eq`.
