<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.executableSmallBiasPolynomial_natDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for the encoded polynomial

**Claim.** The polynomial whose coefficient of $X^{i+1}$ is the image of $\gamma_i$ has natural degree at most $n$.

**Proof.** The polynomial is a finite sum indexed by $i\in\mathrm{Fin}(n)$, and its $i$th summand is a scalar multiple of $X^{i+1}$. The natural degree of a scalar multiple of $X^d$ is at most $d$, so each summand has degree at most $i+1$. Since $i<n$, we have $i+1\le n$. The degree of a finite sum is at most the maximum of the degrees of its summands, hence the whole polynomial has natural degree at most $n$.
