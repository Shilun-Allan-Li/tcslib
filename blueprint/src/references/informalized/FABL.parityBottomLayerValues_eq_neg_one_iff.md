<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityBottomLayerValues_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bottom layer value criterion

**Claim.** The bottom layer value is $-1$ exactly when the normalized sign assignment agrees with the corresponding padded block of input values.

**Proof.** Write $P$ for the equality between the normalized assignment and the corresponding bottom-level input block. Split into the two possibilities. If $P$ holds, the definition of the bottom layer value uses an AND node with a true match, whose value is $-1$; the right side of the claimed equivalence also holds. If $P$ fails, the match is false, so that node has value $1$, and the right side is false. These two cases establish the equivalence.
