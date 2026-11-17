<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallLowDegreeWeightPTF.lean :: FABL.fourierWeightAtMost_onePointFlippedParity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Weight of a Flipped Parity Function

**Claim.** For each $k$, the Fourier weight through degree $k$ of the real-valued one-point-flipped parity function on the $(k+1)$-dimensional sign cube is $(2^{k+1}-1)((1/2)^k)^2$.

**Proof.** On the $(k+1)$-dimensional cube, the only subset of coordinates of size greater than $k$ is the full coordinate set. Consequently, the subsets of size at most $k$ are exactly all subsets except that full set (`lowDegreeFrequencies_eq_erase_univ`). For every such subset $S$, the coefficient formula for the flipped parity function gives $0-(1/2)^k$ (`fourierCoeff_onePointFlippedParity`), so its squared coefficient is $((1/2)^k)^2$. There are $2^{k+1}-1$ subsets other than the full set. Summing their equal weights proves the formula.

**Key facts.** `FABL.lowDegreeFrequencies_eq_erase_univ`, `FABL.fourierCoeff_onePointFlippedParity`.
