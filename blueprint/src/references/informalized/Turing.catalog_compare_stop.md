<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_compare_stop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First stopping position for word comparison

**Claim.** For any two finite words $u$ and $v$, there is an index $d\le\min(|u|,|v|)$ such that their entries agree at every earlier index, they have no common symbol at index $d$, and their symbols-or-absence at $d$ agree exactly when the words are equal.

**Proof.** Induct on $u$, allowing $v$ to vary. If either word is empty, take $d=0$: there are no earlier indices, and at index zero at least one word is absent; agreement of the two optional entries there is equivalent to both words being empty. Now suppose both words are nonempty, say $u=a::u'$ and $v=b::v'$. If $a\ne b$, take $d=0$. The first entries have no common symbol, and their optional entries are equal exactly when the two words are equal, which is impossible in this case. If $a=b$, apply the induction hypothesis to $u',v'$ and let $d'$ be its stopping index. Set $d=d'+1$. Index zero agrees because both first entries are $a$, and every later index below $d$ corresponds to an earlier index below $d'$ in the tails. The stopping condition and the equivalence between agreement of optional entries there and equality of the tails transfer to index $d$. The bound follows by adding one to the tail bound.
