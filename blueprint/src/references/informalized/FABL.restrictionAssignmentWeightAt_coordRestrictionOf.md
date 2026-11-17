<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.restrictionAssignmentWeightAt_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight of a Coordinate Restriction

**Claim.** If the coordinates in $J$ are left free and each coordinate outside $J$ is fixed to its assigned sign, the restriction weight is $\delta^{|J|}((1-\delta)/2)^{n-|J|}$.

**Proof.** At every coordinate, the weight factor is $\delta$ when the coordinate belongs to $J$, and $(1-\delta)/2$ otherwise. For coordinates outside $J$, this follows from `coordRestrictionOf_apply_of_not_mem`: their assigned sign determines which fixed state occurs, and both fixed states have the same weight. Thus the full product factors into one constant product over $J$ and another over its complement. There are $|J|$ factors of the first kind and $n-|J|$ of the second, giving the claimed powers.

**Key facts.** `FABL.coordRestrictionOf_apply_of_not_mem`.
