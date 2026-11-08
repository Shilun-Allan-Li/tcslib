<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaPolynomialSampleCount_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Sample Count Bound

**Claim.** For every coordinate set $P$ and integers $k,b\ge 0$, the polynomial learner’s sample count at the specified per-node failure parameter is bounded by its linear-confidence coefficient times $(n+1)^\ell(b+1)$, where $\ell=k-\lfloor3k/4\rfloor$.

**Proof.** Set $\ell$ to the polynomial degree, let $D$ be the number of degree-at-most-$\ell$ monomials on the coordinates outside $P$, and put $Q=(n+1)^\ell$. First, the count of monomials on those coordinates is at most $(\ell+1)(r+1)^\ell$, where $r$ is the number of coordinates outside $P$ (`lowDegreeF₂MonomialCount_le`). Since $r\le n$ (`juntaRestrictionDimension_le`), this gives $D\le(\ell+1)Q$. The failure-bit contribution is at most the confidence coefficient times $b+1$ (`lowDegreeJuntaQuarterNodeFailureBits_le`). Combining these bounds, and using $Q\ge1$ and $b+1\ge1$, yields $D+$ (failure bits) $\le(\ell+1+C_0)Q(b+1)$, where $C_0$ is the confidence coefficient. Multiplying by $2^\ell$, as in the definition of the sample count, gives the claimed bound by the definition of the linear-confidence coefficient.

**Key facts.** `FABL.lowDegreeF₂MonomialCount_le`, `FABL.juntaRestrictionDimension_le`, `FABL.lowDegreeJuntaQuarterNodeFailureBits_le`.
