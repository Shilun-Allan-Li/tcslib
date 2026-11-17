<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.sum_switchingBadWeight_eq_coordSwitchingFailureProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching Failure Weight Identity

**Claim.** The sum of restriction weights over restrictions for which the restricted function has decision-tree depth at least $k$ equals the coordinate switching failure probability at parameters $\delta$ and $k$.

**Proof.** Expand the switching failure probability as a sum over all coordinate restrictions. For each restriction, its failure indicator is $1$ exactly when the restricted function’s decision-tree depth is at least $k$, and is $0$ otherwise. Thus multiplying by the restriction weight and summing over all restrictions is the same as summing the weights only over those satisfying the depth condition. The latter is precisely the sum over the subtype of switching-bad restrictions; rewriting a sum over such a subtype as a filtered sum over all restrictions gives the claimed equality.
