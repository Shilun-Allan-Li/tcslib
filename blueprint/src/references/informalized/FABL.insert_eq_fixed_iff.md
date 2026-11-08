<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.insert_eq_fixed_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality after insertion

**Claim.** Inserting $i$ into $S$ gives $A$ exactly when $i\in A$ and either $S=A$ or $S=A\setminus\{i\}$.

**Proof.** Suppose first that inserting $i$ into $S$ gives $A$. Then $i\in A$. If $i\in S$, insertion does not change $S$, so $S=A$. If $i\notin S$, the equality says that $A$ consists of $S$ together with $i$; removing $i$ from $A$ recovers $S$. Conversely, if $S=A$ and $i\in A$, inserting $i$ changes nothing. If $S=A\setminus\{i\}$ and $i\in A$, inserting $i$ restores $A$.
