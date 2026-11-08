<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.BoundedCubeFunction.noise_oddPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise commutes with the odd part

**Claim.** For a bounded cube function $f$ and $\rho\in[-1,1]$, taking the odd part after applying noise with parameter $\rho$ gives the same result as applying noise to the odd part of $f$.

**Proof.** By extensionality of bounded cube functions (`FABL.BoundedCubeFunction.ext`), it suffices to compare their underlying functions. Fix an input $x$ and expand each function in the Walsh basis using the Fourier expansion formula (`FABL.fourier_expansion`). The coefficient indexed by a subset $S$ for the noise of a function is its original coefficient multiplied by $\rho^{|S|}$ (`FABL.fourierCoeff_noiseOperator`). The coefficient indexed by $S$ for the odd part is its original coefficient multiplied by $(1-(-1)^{|S|})/2$ (`FABL.fourierCoeff_oddPart`). Applying these two formulas in the two possible orders gives the same coefficient, since the scalar multipliers commute. Thus the two finite sums agree at $x$, and the functions, hence the bounded cube functions, are equal.

**Key facts.** `FABL.BoundedCubeFunction.ext`, `FABL.fourier_expansion`, `FABL.fourierCoeff_noiseOperator`, `FABL.fourierCoeff_oddPart`.
