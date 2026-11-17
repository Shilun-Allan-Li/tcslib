<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.orthogonalComponent_smul_of_uniqueness -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar Linearity of Components

**Claim.** For every real scalar $c$, function $f$, and coordinate set $S$, the $S$-component of $c f$ equals $c$ times the $S$-component of $f$.

**Proof.** Define a candidate decomposition of $c f$ by assigning to each set $T$ the function $c$ times the $T$-component of $f$. Its components sum to $c f$, since the original components sum to $f$ and scalar multiplication distributes over finite sums. Each candidate component depends only on coordinates in its index set, because the original component does. If $T$ is a strict subset of $U$ and $g$ depends only on $T$, the inner product of the candidate $U$-component with $g$ is $c$ times the corresponding inner product for the original decomposition, hence is zero. Thus this is an orthogonal decomposition of $c f$. Uniqueness of the orthogonal decomposition identifies it with the canonical decomposition of $c f$; evaluating at $S$ gives the result.

**Key facts.** `FABL.FiniteFourierBasis.sum_orthogonalComponent`, `FABL.FiniteFourierBasis.orthogonalComponent_dependsOnly`, `FABL.pmfInner_smul_left`, `FABL.FiniteFourierBasis.productInner_orthogonalComponent_eq_zero_of_ssubset`, `FABL.FiniteFourierBasis.orthogonalDecomposition_unique`.
