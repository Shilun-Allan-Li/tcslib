<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.insert_zero_tailFrequency_frequencyTail_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstructing a set from its tail

**Claim.** If $T\subseteq\mathrm{Fin}(n+1)$ contains $0$, then inserting $0$ into the shifted set of positive-index elements of $T$ reconstructs $T$.

**Proof.** Compare membership for each element of $\mathrm{Fin}(n+1)$, splitting into the element $0$ and elements of the form $i+1$. The element $0$ belongs to the reconstructed set by insertion and belongs to $T$ by hypothesis. For an element $i+1$, membership in the shifted tail is equivalent to membership of $i$ in the filtered tail, which by definition is equivalent to $i+1\in T$. Thus the two sets have the same elements.
