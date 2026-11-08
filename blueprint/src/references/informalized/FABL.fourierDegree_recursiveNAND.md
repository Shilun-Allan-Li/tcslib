<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.fourierDegree_recursiveNAND -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of recursive NAND

**Claim.** For every depth $d$, the real-valued recursive NAND function has Fourier degree exactly $2^d$.

**Proof.** The function has $2^d$ input coordinates, so its Fourier degree is at most $2^d$ (`fourierDegree_le_dimension`). If its degree were smaller, it would be at most $2^d-1$. The Fourier degree criterion would then force the Fourier coefficient on the full coordinate set, of size $2^d$, to be zero. This contradicts the nonvanishing of that coefficient (`fourierCoeff_recursiveNAND_univ_ne_zero`). Thus the degree is at least $2^d$ as well, proving equality.

**Key facts.** `FABL.fourierDegree_le_dimension`, `FABL.fourierDegree_le_iff`, `FABL.fourierCoeff_recursiveNAND_univ_ne_zero`.
