<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersDiagonalInner_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of the Diagonal Inner Product

**Claim.** For any real number $a$ and any real-valued function $f$ on the Boolean cube, scaling $f$ by $a$ scales its diagonal Gowers inner product of order $k$ by $a^{2^k}$.

**Proof.** In the defining product for the diagonal inner product, each of the $2^k$ indices contributes a factor of $a$. Thus the product of function values acquires the factor $a^{2^k}$, using that the $k$-dimensional Boolean cube has cardinality $2^k$ (\texttt{FABL.card_f₂Cube}). This factor is independent of the averaging variables, so it can be pulled out of each finite average. The remaining iterated average is the original diagonal inner product, yielding the stated homogeneity.

**Key facts.** `FABL.card_f₂Cube`.
