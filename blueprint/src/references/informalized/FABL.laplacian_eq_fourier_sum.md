<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/LaplacianAndPoincare.lean :: FABL.laplacian_eq_fourier_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier expansion of the Laplacian

**Claim.** The Laplacian of a real-valued function at a point is the Fourier sum weighted by the cardinality of each frequency set: $Lf(x)=\sum_S |S|\widehat f(S)\chi_S(x)$.

**Proof.** First express the Laplacian at $x$ as the sum over coordinates of the coordinate Laplacians (FABL.laplacian_apply). For each coordinate, the coordinate Fourier formula (FABL.coordinateLaplacian_eq_fourier_sum) writes its contribution as a sum over frequency sets containing that coordinate, with summand $\widehat f(S)\chi_S(x)$. Interchange the two finite sums: for each fixed $S$, its summand then appears once for every coordinate in $S$. There are $|S|$ such coordinates, so the inner sum is $|S|\widehat f(S)\chi_S(x)$, giving the formula.

**Key facts.** `FABL.laplacian_apply`, `FABL.coordinateLaplacian_eq_fourier_sum`.
