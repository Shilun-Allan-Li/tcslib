<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ReasonableProductPolynomials.lean :: FABL.multilinearEvenCoefficients_degreeAtMost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound for Even Coefficients

**Claim.** If the coefficient function vanishes on every subset of size greater than $k$, then the coefficients obtained by shifting positions up by one also vanish on every subset of size greater than $k$.

**Proof.** Take a subset $S$ of the smaller index set with $|S|>k$. Its shifted subset has the same cardinality, since shifting is an embedding and hence preserves the number of elements. Thus the shifted subset also has size greater than $k$, so the assumed degree bound for the original coefficients makes its coefficient zero. By definition, this is the new coefficient assigned to $S$.

**Key facts.** `FABL.card_tailFrequency`.
