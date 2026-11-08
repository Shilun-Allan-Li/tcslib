<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/PrefixBuckets.lean :: FABL.liftFreeFrequency_freeFrequencyPart_eq_of_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting the restricted subset

**Claim.** For finite subsets $J,S$ of $\mathrm{Fin}(n)$ with $S\subseteq J$, viewing the elements of $S$ as elements indexed by $J$ and then as elements of $\mathrm{Fin}(n)$ recovers exactly $S$.

**Proof.** Compare membership of an arbitrary $i\in\mathrm{Fin}(n)$ in the lifted restricted part and in $S$. Membership in the lifted image means that $i$ is the underlying index of some element $j$ of $J$ that lies in the restricted part. By the characterization of membership in that part (\(\mathrm{FABL.mem\_freeFrequencyPart}\)), this is equivalent to $i\in S$. Conversely, if $i\in S$, the inclusion $S\subseteq J$ lets us regard $i$ as an element of $J$; it belongs to the restricted part and maps back to $i$. Hence the sets agree.

**Key facts.** `FABL.mem_freeFrequencyPart`.
