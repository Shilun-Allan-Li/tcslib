<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.width_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width bounded by dimension

**Claim.** Every DNF term on $n$ coordinates has width at most $n$.

**Proof.** The support of the term is a subset of the $n$ coordinates, so its cardinality is at most $n$. The support-cardinality identity identifies this cardinality with the term's width (card_support). Hence the width is at most $n$.

**Key facts.** `FABL.DNFTerm.card_support`.
