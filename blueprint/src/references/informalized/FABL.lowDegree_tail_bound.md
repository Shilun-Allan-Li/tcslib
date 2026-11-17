<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.lowDegree_tail_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree tail bound

**Claim.** If $f$ has Fourier degree at most $k$ with $k>0$ and positive $L^2$ norm, then for $t\ge(2e)^{k/2}$, the probability that $|f|$ is at least $t\|f\|_2$ is bounded by $\exp\!\left(-\frac{k}{2e}t^{2/k}\right)$.

**Proof.** Write $K=k$, $E=e$, $u=t^{2/K}$, and $q=u/E$. Since $t\ge(2E)^{K/2}>0$, raising the inequality to the positive power $2/K$ gives $u\ge2E$, so $q\ge2$. Apply the parameterized tail estimate (`lowDegree_tail_bound_parameter`) with this $q$ and the given $t$ to bound the desired probability by $(q^{K/2}/t)^q$. The definitions give $u^{K/2}=t$, and hence $q^{K/2}/t=e^{-K/2}$. The bound becomes $\exp((-K/2)q)$. Substituting $q=u/E$ and $u=t^{2/K}$ yields $\exp(-K t^{2/K}/(2e))$, which is the asserted expression.

**Key facts.** `FABL.lowDegree_tail_bound_parameter`.
