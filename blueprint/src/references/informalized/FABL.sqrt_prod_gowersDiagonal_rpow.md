<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.sqrt_prod_gowersDiagonal_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square Root of a Product of Diagonal Averages

**Claim.** For $k>0$, $r\in\mathbb N$, and a family $F$ as stated, the square root of the product of the diagonal averages raised to $1/2^r$ equals the product of those same averages raised to $1/2^{r+1}$.

**Proof.** For each point $s$ of the $r$-dimensional cube, put $a_s=D_k(F_s)$. Since $k>0$, it has the form $q+1$ for some natural number $q$, and the nonnegativity theorem for diagonal averages (`gowersDiagonalInner_nonneg`) gives $a_s\ge0$. Hence every factor $a_s^{1/2^r}$ is nonnegative. The square root of a finite product of nonnegative reals is the product of their square roots, so the left side becomes $\prod_s (a_s^{1/2^r})^{1/2}$. For nonnegative bases, exponents multiply under real powers, giving $\prod_s a_s^{(1/2^r)(1/2)}=\prod_s a_s^{1/2^{r+1}}$, as required.

**Key facts.** `FABL.gowersDiagonalInner_nonneg`.
