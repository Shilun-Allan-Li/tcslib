<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/CorrelationImmunityBounds.lean :: FABL.card_add_card_add_card_symmDiff_le_two_mul_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric difference cardinality bound

**Claim.** For subsets $S,T$ of an $n$-element set, $|S|+|T|+|S\mathbin{\triangle}T|\le2n$.

**Proof.** The two differences $S\setminus T$ and $T\setminus S$ are disjoint, and their union is the symmetric difference. Thus $|S\mathbin{\triangle}T|=|S\setminus T|+|T\setminus S|$. The cardinality identities for a set and its difference with another set express $|S|$ and $|T|$ as the corresponding difference sizes plus their intersection size. The union-cardinality identity expresses $|S|+|T|$ as $|S\cup T|+|S\cap T|$. Combining these identities, the left side becomes $|S\cup T|+2|S\setminus T|+2|S\cap T|$, equivalently $2|S\cup T|$; since $S\cup T$ is contained in the $n$-element ambient set, this is at most $2n$.
