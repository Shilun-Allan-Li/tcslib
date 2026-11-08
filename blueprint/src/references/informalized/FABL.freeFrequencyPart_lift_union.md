<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.freeFrequencyPart_lift_union -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free Part of a Split Frequency Set

**Claim.** If $S$ is a subset of $J$ and $T$ is a subset of the complementary coordinates, then the part inside $J$ of the union of their lifts is $S$.

**Proof.** A coordinate in $J$ belongs to the union of the lifted sets exactly when it belongs to the lift of $S$: no coordinate in the lift of $T$ lies in $J$, since every coordinate of $T$ lies outside $J$. The lift of $S$ contains precisely the coordinates represented by members of $S$. Thus the union's part inside $J$ consists exactly of the members of $S.
