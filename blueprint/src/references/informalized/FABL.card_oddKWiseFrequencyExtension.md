<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.card_oddKWiseFrequencyExtension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of the Odd Frequency Extension

**Claim.** The family formed by adjoining coordinate $i$ to each $m$-element subset of the other $n-1$ coordinates has cardinality $\binom{n-1}{m}$.

**Proof.** Start with the $m$-element subsets of the coordinates other than $i$, and map each such subset $S$ to $S\cup\{i\}$. This map is injective: because $i\notin S$, removing $i$ from the image recovers $S$. Thus the image family has the same cardinality as its domain. The domain consists of the $m$-element subsets of a set of size $n-1$, so its cardinality is $\binom{n-1}{m}$.
