<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.fourierCoeff_recursiveMajorityThree_univ_eq_addressTopCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Top coefficient of recursive majority

**Claim.** For every depth $d$, the Fourier coefficient on all coordinates of the depth-$d$ recursive ternary majority function equals the top correlation of the corresponding recursive majority formula on its leaf addresses.

**Proof.** Reindex the leaf coordinates of the sign cube by the bijection between coordinate indices and formula addresses. The top-correlation reindexing identity preserves the expectation defining top correlation under this bijection (\(\texttt{FABL.topCorrelation_reindex}\)). After writing both quantities as expectations, the recursive majority function agrees pointwise with the address-based recursive majority formula, with its inputs read through the inverse coordinate bijection (\(\texttt{FABL.recursiveMajorityThree_eq_addressRecursiveMajorityThree}\)). Under this same reindexing, the product of all coordinate signs is the product of the signs at all leaf addresses. Thus the two expectation integrands agree, proving the equality.

**Key facts.** `FABL.topCorrelation_reindex`, `FABL.recursiveMajorityThree_eq_addressRecursiveMajorityThree`.
