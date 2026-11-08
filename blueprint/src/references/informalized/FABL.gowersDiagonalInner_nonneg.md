<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersDiagonalInner_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Diagonal Inner Product

**Claim.** For every $k\geq0$ and every real-valued function $f$ on the Boolean cube, the diagonal Gowers inner product of order $k+1$ is nonnegative.

**Proof.** Take the constant family $F$ on the $(k+1)$-dimensional index cube, with value $f$ at every index. Duplicating one coordinate of a family with the fixed value $0$ leaves this constant family unchanged. The diagonal inner product of order $k+1$ is therefore the inner product of this duplicated family. The nonnegativity theorem for an inner product with a duplicated coordinate (\texttt{FABL.gowersInner_duplicateAt_nonneg}) gives the result.

**Key facts.** `FABL.gowersInner_duplicateAt_nonneg`.
