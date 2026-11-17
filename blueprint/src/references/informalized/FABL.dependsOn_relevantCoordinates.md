<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.dependsOn_relevantCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dependence on Relevant Coordinates

**Claim.** A real-valued function on the sign cube takes equal values at any two inputs that agree on every relevant coordinate.

**Proof.** Expand $f$ at each of the two inputs using its Fourier expansion (\texttt{fourier\_expansion}). Compare the terms indexed by each subset $S$. If the Fourier coefficient is zero, both terms vanish. Otherwise, every coordinate $i\in S$ is relevant, by the fact that a nonzero Fourier coefficient makes each coordinate in its support relevant (\texttt{isRelevant\_of\_fourierCoeff\_ne\_zero}). The two inputs agree on those coordinates, so their monomials on $S$ agree. Thus corresponding terms in the two expansions are equal, and summing shows the function values agree.

**Key facts.** `FABL.fourier_expansion`, `FABL.isRelevant_of_fourierCoeff_ne_zero`.
