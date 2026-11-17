<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.orthogonalComponent_add_of_uniqueness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of orthogonal components

**Claim.** For functions $f$ and $g$ on the product space and any coordinate set $S$, the orthogonal component of $f+g$ at $S$ is the sum of their orthogonal components at $S$.

**Proof.** Define a candidate decomposition of $f+g$ by assigning to each coordinate set $T$ the sum of the orthogonal components of $f$ and $g$ at $T$. Summing these candidate components over all $T$ gives $f+g$, since the orthogonal components of each function sum to that function ($\texttt{FABL.FiniteFourierBasis.sum_orthogonalComponent}$). Each candidate component depends only on coordinates in $T$: if two inputs agree on $T$, both component values agree, by the dependence property for each function ($\texttt{FABL.FiniteFourierBasis.orthogonalComponent_dependsOnly}$).

It remains to check the required orthogonality. For any strict subset $U\subsetneq T$ and any function depending only on $U$, the inner product of the candidate component at $T$ with that function splits as the sum of the two inner products, by linearity in the first argument ($\texttt{FABL.pmfInner_add_left}$). Each is zero by the orthogonality property of an individual component against functions depending on a strict subset ($\texttt{FABL.FiniteFourierBasis.productInner_orthogonalComponent_eq_zero_of_ssubset}$). Thus the candidate is an orthogonal decomposition of $f+g$. Uniqueness of that decomposition identifies it with the given orthogonal components ($\texttt{FABL.FiniteFourierBasis.orthogonalDecomposition_unique}$), yielding the claimed equality at $S$.

**Key facts.** `FABL.FiniteFourierBasis.sum_orthogonalComponent`, `FABL.FiniteFourierBasis.orthogonalComponent_dependsOnly`, `FABL.pmfInner_add_left`, `FABL.FiniteFourierBasis.productInner_orthogonalComponent_eq_zero_of_ssubset`, `FABL.FiniteFourierBasis.orthogonalDecomposition_unique`.
