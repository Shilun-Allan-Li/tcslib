<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.coordinateProjection_fixProductCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection commutes with fixing another coordinate

**Claim.** When $i$ and $j$ are distinct, projecting away coordinate $i$ commutes with fixing coordinate $j$ to a specified value.

**Proof.** Evaluate both functions at an arbitrary input $x$. Both are averages over the same resampled inputs, so it suffices to compare their integrands. At coordinate $j$, both constructions use the specified fixed value; at coordinate $i$, both use the resampled value; and at every other coordinate, both retain the original value from $x$. The distinctness of $i$ and $j$ ensures these assignments do not conflict. Hence the merged inputs, and therefore their function values and averages, agree.
