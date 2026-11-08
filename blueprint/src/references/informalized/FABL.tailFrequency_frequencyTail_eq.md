<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.tailFrequency_frequencyTail_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a set from its tail frequencies

**Claim.** If a finite set of indices in $\{0,1,\ldots,n\}$ omits $0$, then shifting up the indices obtained by deleting the initial coordinate recovers exactly the original set.

**Proof.** We check membership at each index. At the initial index $0$, the shifted set has no element, and the original set has none by hypothesis. Every other index is uniquely $i+1$ for some $i\in\{0,\ldots,n-1\}$. By definition, $i$ belongs to the tail precisely when $i+1$ belongs to the original set; the embedding that shifts indices sends $i$ to $i+1$. Thus the two sets have identical membership at every index.
