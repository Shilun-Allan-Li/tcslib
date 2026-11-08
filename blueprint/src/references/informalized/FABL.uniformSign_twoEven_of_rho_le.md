<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.uniformSign_twoEven_of_rho_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even-Exponent Affine Contraction

**Claim.** For $r>0$, nonnegative $\rho\le1/\sqrt{2r-1}$ guarantees that every affine function of a uniform sign contracts from the $L^2$ norm to the $L^{2r}$ norm.

**Proof.** Since $r$ is a positive integer, split into $r=1$ and $r>1$. When $r=1$, the claimed bound says $\rho\le1$. The explicit formula for the $L^2$ norm of an affine function of a uniform sign is $\sqrt{a^2+b^2}$ ($\texttt{uniformLpNorm_two_affineSign}$); substituting this formula on both sides, the inequality follows from $\rho^2\le1$ and $b^2\ge0$. When $r>1$, put $q=2r$, so $q>2$. The sharp one-bit $(2,q)$ estimate applies with the assumed nonnegative $\rho$ and the bound $\rho\le1/\sqrt{q-1}$, giving the result ($\texttt{oneBit_twoQ}$).

**Key facts.** `FABL.uniformLpNorm_two_affineSign`, `FABL.oneBit_twoQ`.
