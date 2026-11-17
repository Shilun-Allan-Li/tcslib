<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.fourierCoeff_recursiveNAND_univ_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of the recursive NAND coefficient

**Claim.** For every depth $d$, the Fourier coefficient on all coordinates of the recursive NAND function is nonzero.

**Proof.** The Fourier coefficient equals the top correlation of the address-based recursive NAND formula by the coefficient-to-correlation identity (\(\texttt{FABL.fourierCoeff_recursiveNAND_univ_eq_addressTopCoeff}\)). That top correlation is nonzero at every depth (\(\texttt{FABL.addressRecursiveNANDTopCoeff_ne_zero}\)); substituting the equality gives the result.

**Key facts.** `FABL.fourierCoeff_recursiveNAND_univ_eq_addressTopCoeff`, `FABL.addressRecursiveNANDTopCoeff_ne_zero`.
