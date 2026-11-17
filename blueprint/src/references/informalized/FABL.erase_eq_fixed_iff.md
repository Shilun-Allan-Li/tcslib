<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.erase_eq_fixed_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-set erasure characterization

**Claim.** Deleting $i$ from $S$ gives $A$ exactly when $i\notin A$ and either $S=A$ or $S=A\cup\{i\}$.

**Proof.** Suppose first that $S\setminus\{i\}=A$. Then $i$ cannot belong to $A$, since it was deleted. If $i\in S$, restoring the deleted element gives $S=A\cup\{i\}$; if $i\notin S$, erasing it changes nothing, so $S=A$. Conversely, if $i\notin A$ and $S=A$, erasing $i$ leaves $A$ unchanged. If instead $S=A\cup\{i\}$, erasing $i$ leaves precisely $A$.
