<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNAND_even_eq_iteratedTribesTwoTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Recursive NAND as Iterated Tribes

**Claim.** For every $k$ and every sign assignment $x$ to the $2^{2k}$ coordinates, recursive NAND of depth $2k$ equals iterated tribes of depth $k$ on the assignment reindexed by the canonical bijection from the $2^{2k}$ coordinates to the $4^k$ coordinates.

**Proof.** First rewrite recursive NAND as address-recursive NAND using the canonical coordinate-to-address equivalence (`recursiveNAND_eq_addressRecursiveNAND`). Define an assignment on arity-four addresses by sending each address to the original input coordinate corresponding, under the arity-two indexing equivalence, to its image under the even-depth address equivalence. The even-address identity (`addressRecursiveNAND_even_eq_iteratedTribes`) says that address-recursive NAND at depth $2k$, evaluated on this reindexed assignment, equals address-based iterated tribes at depth $k$. Unfolding the coordinate reindexing and the definition of iterated tribes shows this right-hand side is exactly iterated tribes applied to $x$ through the stated canonical coordinate bijection.

**Key facts.** `FABL.recursiveNAND_eq_addressRecursiveNAND`, `FABL.addressRecursiveNAND_even_eq_iteratedTribes`.
