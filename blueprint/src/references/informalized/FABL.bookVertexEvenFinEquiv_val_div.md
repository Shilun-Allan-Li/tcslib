<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.bookVertexEvenFinEquiv_val_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Index of an even-partite book vertex

**Claim.** For $k>0$, dividing the enumerated index of a vertex in the book with $2r$ parts and $k$ vertices per part by $k$ gives the index of its part.

**Proof.** The even-partite enumeration is the general book-vertex enumeration followed by the identification of its target index set with the indices up to $2rk$. Thus the general enumeration's quotient formula applies: its index divided by $k$ is the part index. Rewriting the enumeration in its even-partite form yields the stated equality.

**Key facts.** `FABL.bookVertexFinEquiv_val_div`.
