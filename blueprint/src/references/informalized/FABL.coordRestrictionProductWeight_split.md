<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordRestrictionProductWeight_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product weight across a coordinate split

**Claim.** The product weight for the assignment formed from restrictions on $J$ and its complement factors as the product of the two weights on those parts.

**Proof.** Use the bijection that identifies each coordinate with either an element of $J$ or an element of its complement. Reindexing the product over all coordinates by this bijection turns it into a product over the disjoint union $J\sqcup\mathrm{FixedIndex}(J)$. The finite product over a disjoint union factors into the product over each summand. On the first summand, the combined assignment evaluates to the given restriction on $J$; on the second, it evaluates to the given restriction on the complement. These coordinatewise identifications yield the two claimed factors.
