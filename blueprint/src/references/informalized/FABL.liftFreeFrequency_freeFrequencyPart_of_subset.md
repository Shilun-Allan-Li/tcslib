<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.liftFreeFrequency_freeFrequencyPart_of_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting the restricted subset

**Claim.** For finite subsets $J,S$ of $\mathrm{Fin}(n)$ with $S\subseteq J$, viewing the elements of $S$ as elements indexed by $J$ and then in $\mathrm{Fin}(n)$ recovers exactly $S$.

**Proof.** For any $i\in\mathrm{Fin}(n)$, membership in the lifted image means that $i$ is the underlying index of some element of $J$ that belongs to the restricted part of $S$. That membership is precisely the condition that the underlying index lies in $S$. Thus every element of the lifted image belongs to $S$. Conversely, if $i\in S$, the inclusion $S\subseteq J$ makes $i$ an element of $J$, and this element belongs to the restricted part and maps to $i$. The two sets therefore have identical membership.
