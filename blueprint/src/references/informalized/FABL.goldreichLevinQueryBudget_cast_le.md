<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevinAlgorithm/Resources.lean :: FABL.goldreichLevinQueryBudget_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Goldreich–Levin query budget bound

**Claim.** The Goldreich–Levin query budget is at most $2^{21}n(n+1)/\tau^8$.

**Proof.** Let $C$ be the active cap and $m$ the estimator’s sample count for the specified accuracy and confidence. The sample-count estimate gives $m\le5120(n+1)(C+1)/\tau^4$ (`goldreichLevinSampleCount_cast_le`), while the active-cap estimates give $C\le8/\tau^2$ and $C+1\le9/\tau^2$ (`goldreichLevinActiveCap_cast_le`, `goldreichLevinActiveCap_add_one_cast_le`). By the definition of the query budget, its rational value is $4nCm$. Substituting the bounds on $C$ and $m$ yields
\[
4n\frac{8}{\tau^2}\cdot\frac{5120(n+1)(C+1)}{\tau^4}
\le \frac{1{,}474{,}560\,n(n+1)}{\tau^8}.
\]
Using $C+1\le9/\tau^2$ in this estimate gives the displayed constant. Since $1{,}474{,}560\le2^{21}$, the claimed budget bound follows.

**Key facts.** `FABL.goldreichLevinSampleCount_cast_le`, `FABL.goldreichLevinActiveCap_cast_le`, `FABL.goldreichLevinActiveCap_add_one_cast_le`.
