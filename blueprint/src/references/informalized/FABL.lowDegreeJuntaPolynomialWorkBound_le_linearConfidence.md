<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaPolynomialWorkBound_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Learner Work Bound

**Claim.** For every coordinate set $P$ and integers $k,b\ge0$, the polynomial learner’s work is at most its work coefficient times $(n+1)^{3\ell}(b+1)$, where $\ell=k-\lfloor3k/4\rfloor$.

**Proof.** Write $D$ for the monomial count, $m$ for the sample count, and $Q=(n+1)^\ell$. The monomial-count bound together with $r\le n$ gives $D\le(\ell+1)Q$ (`lowDegreeF₂MonomialCount_le`, `juntaRestrictionDimension_le`); the sample-count bound gives $m\le C Q(b+1)$ (`lowDegreeJuntaPolynomialSampleCount_le_linearConfidence`), where $C$ is the sample coefficient. Since $Q\ge1$ and $b+1\ge1$, these imply $D+1\le(\ell+2)Q$ and $D+2\le(\ell+3)Q$. Bound the three work terms separately: $m(D+1)$ by $C(\ell+2)Q^3(b+1)$, $Dm(D+2)$ by $(\ell+1)C(\ell+3)Q^3(b+1)$, and $D(D+1)$ by $(\ell+1)(\ell+2)Q^3(b+1)$. Adding them gives the stated coefficient times $Q^3(b+1)$. Finally, $Q^3=(n+1)^{3\ell}$.

**Key facts.** `FABL.lowDegreeF₂MonomialCount_le`, `FABL.juntaRestrictionDimension_le`, `FABL.lowDegreeJuntaPolynomialSampleCount_le_linearConfidence`.
