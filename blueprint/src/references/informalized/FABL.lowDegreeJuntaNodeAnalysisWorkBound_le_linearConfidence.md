<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaNodeAnalysisWorkBound_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Node Analysis Work Bound

**Claim.** For natural numbers $n,k,b$ and a coordinate set $P$ among the $n$ coordinates, the node analysis work bound at the per-call failure obtained from the dyadic failure parameter with $b$ bits is at most the node analysis linear coefficient at $k$ times $(n+1)^{\lfloor 3k/4\rfloor+3}(b+1)$.

**Proof.** Let $B=(n+1)^{\lfloor 3k/4\rfloor+3}$. The node analysis bound has four contributions: Fourier estimation, polynomial learning, the size of the Fourier family, and the number of low-degree monomials. The Fourier batch estimate bounds the first contribution by its linear coefficient times $(n+1)^{\lfloor 3k/4\rfloor+1}(b+1)$, with the additional cutoff factor in the work bound. The polynomial work estimate bounds the second by its linear coefficient times $(n+1)^{3d}(b+1)$, where $d$ is the polynomial degree. The Fourier family cardinality bound controls the third by $(\lfloor 3k/4\rfloor+1)(n+1)^{\lfloor 3k/4\rfloor}$, and the monomial count bound controls the fourth by $(d+1)(r+1)^d$, where $r$ is the dimension of the free coordinates. Since $r\le n$, the latter is at most $(d+1)(n+1)^d. The runtime exponent ledger gives $3d\le \lfloor 3k/4\rfloor+3$; the cutoff exponent and $d$ are also at most this exponent. Thus each power of $n+1$ above is at most $B$. For the two terms not already carrying the factor $b+1$, use $1\le b+1$. Adding these four estimates and factoring out $B(b+1)$ leaves exactly the node analysis linear coefficient.

**Key facts.** `FABL.lowDegreeJuntaFourierBatchSize_le_linearConfidence`, `FABL.lowDegreeJuntaPolynomialWorkBound_le_linearConfidence`, `FABL.card_lowDegreeJuntaFourierFamily_le`, `FABL.lowDegreeF₂MonomialCount_le`, `FABL.juntaRestrictionDimension_le`, `FABL.lowDegreeJuntaRuntimeExponentLedger`.
