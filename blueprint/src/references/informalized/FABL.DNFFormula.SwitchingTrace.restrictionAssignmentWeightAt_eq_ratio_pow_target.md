<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.SwitchingTrace.restrictionAssignmentWeightAt_eq_ratio_pow_target -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Weight Along a Trace

**Claim.** For a switching trace of length $k$ and any $\delta<1$, the initial restriction’s weight equals $\left(\frac{2\delta}{1-\delta}\right)^k$ times the target restriction’s weight.

**Proof.** Proceed by induction on the trace. In the final case, let $T$ be the canonical term and take the coordinates indexed by the chosen positions. Each is free in the initial restriction, by the position-subset condition and the characterisation of free literal positions. Fixing these distinct coordinates with the term’s satisfying assignment multiplies the restriction weight by the switching ratio once per coordinate. Their number is $k+1$, as required for this terminal trace.

For a cons trace, let $T$ be its canonical term, let the coordinates be those at all its free literal positions, and let $\eta$ be the restriction obtained by fixing these coordinates using the trace’s assignment. The coordinates are distinct and free initially, so fixing them gives the initial weight as the ratio to the power of their number times the weight of $\eta$ (the weight-change formula, `FABL.restrictionAssignmentWeightAt_fixCoordinateList`). By induction, the weight of $\eta$ is the ratio to the power of the tail length times the tail target’s weight.

The target extension property shows that the tail target keeps every coordinate fixed by $\eta$. Thus every coordinate in this block is already fixed there. Fixing the same coordinates again to form the outer restriction does not change its weight, by the weight invariance for lists of already-fixed coordinates (`FABL.restrictionAssignmentWeightAt_fixCoordinateList_of_all_fixed`). Finally, the block has length $i+1$, and the tail has length $k-i$; their sum is $k+1$. Combining the powers yields the claimed formula for the cons trace.

**Key facts.** `FABL.DNFFormula.SwitchingTrace.target_extends`, `FABL.DNFTerm.coordinatesAtPositions_nodup`, `FABL.DNFTerm.coordinatesAt_freeLiteralPositions_all_free`, `FABL.restrictionAssignmentWeightAt_fixCoordinateList`, `FABL.restrictionAssignmentWeightAt_fixCoordinateList_of_all_fixed`.
