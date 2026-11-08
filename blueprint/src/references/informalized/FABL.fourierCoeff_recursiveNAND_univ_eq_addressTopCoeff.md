<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.fourierCoeff_recursiveNAND_univ_eq_addressTopCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Top coefficient of recursive NAND

**Claim.** For every depth $d$, the Fourier coefficient on all coordinates of the depth-$d$ recursive NAND function equals the top correlation of the corresponding recursive NAND formula on its leaf addresses.

**Proof.** Reindex the input coordinates by the bijection from coordinate indices to formula addresses. Top correlation is unchanged by this reindexing (\(\texttt{FABL.topCorrelation_reindex}\)). The recursive NAND function agrees pointwise with the address-based recursive NAND formula when its inputs are read through the inverse bijection (\(\texttt{FABL.recursiveNAND_eq_addressRecursiveNAND}\)). The product of all input signs becomes the product over all leaf addresses, so the expectation integrands agree and the Fourier coefficient equals the stated top correlation.

**Key facts.** `FABL.topCorrelation_reindex`, `FABL.recursiveNAND_eq_addressRecursiveNAND`.
