<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.card_le_card_symmDiff_singleton_add_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality under symmetric difference

**Claim.** For a finite set $S\subseteq\{0,\ldots,n-1\}$ and an element $i$ of this ground set, $|S|\leq|S\mathbin{\triangle}\{i\}|+1$.

**Proof.** Every element of $S$ either is $i$, or differs from $i$ and therefore remains in the symmetric difference $S\mathbin{\triangle}\{i\}$. Thus $S\subseteq(S\mathbin{\triangle}\{i\})\cup\{i\}$. The cardinality of a union is at most the sum of the cardinalities, and the singleton has size one. Combining these facts gives the claimed inequality.
