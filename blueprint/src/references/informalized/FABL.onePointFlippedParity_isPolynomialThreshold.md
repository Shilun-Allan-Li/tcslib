<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallLowDegreeWeightPTF.lean :: FABL.onePointFlippedParity_isPolynomialThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold degree of flipped parity

**Claim.** For every natural number $k$, parity on the $(k+1)$-dimensional sign cube with its value flipped at the all-ones input has a polynomial threshold representation of Fourier degree at most $k$.

**Proof.** Apply the general result that any Boolean function on a positive-dimensional sign cube which is neither full parity nor its negative has a polynomial threshold representation of degree at most one less than the dimension (`isPolynomialThreshold_pred_of_ne_parityFunction_univ`). The cube dimension is $k+1$, which is positive, and the one-point-flipped function differs from full parity and from its negative by the two comparison results `onePointFlippedParity_ne_fullParity` and `onePointFlippedParity_ne_neg_fullParity`. The general result therefore gives degree at most $(k+1)-1=k$.

**Key facts.** `FABL.isPolynomialThreshold_pred_of_ne_parityFunction_univ`, `FABL.onePointFlippedParity_ne_fullParity`, `FABL.onePointFlippedParity_ne_neg_fullParity`.
