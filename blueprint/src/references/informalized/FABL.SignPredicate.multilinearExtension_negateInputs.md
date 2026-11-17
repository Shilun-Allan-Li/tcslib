<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.SignPredicate.multilinearExtension_negateInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negating Inputs in the Multilinear Extension

**Claim.** Negating the selected inputs of a predicate and evaluating its multilinear extension at $\mu$ gives the same value as evaluating the original predicate’s multilinear extension at the vector with the selected coordinates negated.

**Proof.** Expand both multilinear extensions as sums over subsets $S$ of coordinates and compare their summands. The Fourier coefficient of the indicator of the input-negated predicate is the original coefficient multiplied by $\prod_{i\in S}(-1)$ over selected coordinates (and by $1$ over the others), by the Fourier-coefficient transformation rule (\texttt{FABL.fourierCoeff_indicator_negateInputs}). Meanwhile, the product of the modified coordinates over $S$ is exactly this same sign factor times the product of the original coordinates over $S$. Thus each summand agrees, and so do the sums.

**Key facts.** `FABL.fourierCoeff_indicator_negateInputs`.
