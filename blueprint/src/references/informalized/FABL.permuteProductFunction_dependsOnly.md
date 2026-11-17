<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.permuteProductFunction_dependsOnly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate dependence under permutation

**Claim.** If a function depends only on the coordinates in $S$, then the function obtained by permuting its inputs by $\sigma$ depends only on the coordinates in $\sigma(S)$.

**Proof.** Take two inputs that agree on $\sigma(S)$. To compare the permuted function on them, apply the original function's dependence property. For every $i\in S$, the permuted inputs agree at coordinate $i$, since the original inputs agree at coordinate $\sigma(i)\in\sigma(S)$. Thus the function values agree, as required.
