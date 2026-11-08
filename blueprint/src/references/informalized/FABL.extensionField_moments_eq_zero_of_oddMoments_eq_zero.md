<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ReducedVandermonde.lean :: FABL.extensionField_moments_eq_zero_of_oddMoments_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vanishing of Low Order Moments

**Claim.** If the sum of the zeroth powers over $S$ vanishes and every odd power sum of degree below $k$ vanishes, then every power sum of degree below $k$ vanishes.

**Proof.** Use strong induction on the exponent $p$, proving the assertion for all exponents below $k$. Write $p$ as either $2q$ or $2q+1$. In the odd case, the desired vanishing is exactly the assumed odd-moment condition. In the even case, if $q=0$, the sum is the assumed sum of ones. Otherwise $q<2q=p$, so strong induction gives $\sum_{j\in S}\alpha_j^q=0$; also $q<k$. For each $j$, $\alpha_j^{2q}=(\alpha_j^q)^2$. In characteristic two, the square of a finite sum is the sum of the squares (\texttt{CharTwo.sum_sq}), so $\sum_{j\in S}\alpha_j^{2q}=(\sum_{j\in S}\alpha_j^q)^2=0$. This proves the induction step in both cases.
