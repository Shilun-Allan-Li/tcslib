<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.restrictProductCoordinate_dependsOnly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Restriction and Dependence

**Claim.** If a real-valued function depends only on coordinates in $S$, then replacing coordinate $i$ by a fixed value yields a function depending only on $S\setminus\{i\}$.

**Proof.** Take two inputs that agree on $S\setminus\{i\}$ and apply the original function after replacing coordinate $i$ by the fixed value. To use the assumed dependence of the original function, check agreement on every coordinate of $S$. If the coordinate is $i$, the replacements make the two inputs equal there. If it is different from $i$, it belongs to $S\setminus\{i\}$, so the inputs already agree there; replacing coordinate $i$ does not change it. The original function therefore has equal values on the two replaced inputs, as required.
