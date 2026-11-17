<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.mem_oddKWiseFrequencyExtension_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of an odd frequency extension member

**Claim.** If $S$ belongs to the family formed by adjoining $i$ to each $m$-element subset of the other indices, then $i\in S$ and $|S|=m+1$.

**Proof.** By membership in the image defining the extension family, there is an $m$-element set $T$ among the indices other than $i$ such that $S=\{i\}\cup T$. In particular, $i\notin T$, since $T$ lies in the family of subsets of the universal set with $i$ erased. Hence $i\in S$, and adjoining an element not already in $T$ increases its cardinality by one. Since $|T|=m$, it follows that $|S|=m+1$.
