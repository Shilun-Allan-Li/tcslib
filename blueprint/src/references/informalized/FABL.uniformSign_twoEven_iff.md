<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.uniformSign_twoEven_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp Even-Exponent Contraction Criterion

**Claim.** For positive integer $r$ and nonnegative $\rho$, the affine contraction inequality from $L^2$ to $L^{2r}$ holds for every $a,b$ exactly when $\rho\le 1/\sqrt{2r-1}$.

**Proof.** The forward implication uses the necessary squared bound: if the affine inequality holds for all $a,b$, then $\rho^2\le 1/(2r-1)$ ($\texttt{uniformSign_twoEven_necessary_sq}$). Since $r>0$, the quantity $2r-1$ is positive. Taking square roots, using $\rho\ge0$, and rearranging yields $\rho\le1/\sqrt{2r-1}$. Conversely, when this sharp bound holds, the sufficient even-exponent estimate gives the affine inequality for every $a,b$ ($\texttt{uniformSign_twoEven_of_rho_le}$).

**Key facts.** `FABL.uniformSign_twoEven_necessary_sq`, `FABL.uniformSign_twoEven_of_rho_le`.
