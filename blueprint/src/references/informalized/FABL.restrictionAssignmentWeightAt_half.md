<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.restrictionAssignmentWeightAt_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight at parameter one half

**Claim.** At parameter $1/2$, the assignment weight equals the ordinary product weight, whose coordinate factors are $1/2$ for free coordinates and $1/4$ for either fixed state.

**Proof.** Expand both assignment weights as products over the coordinates. At each coordinate, there are three possible states: for a free state, the parameter-dependent factor is $1/2$; for either fixed state, it is $(1-1/2)/2=1/4$. These are exactly the corresponding ordinary coordinate weights. Since the factors agree at every coordinate, the products agree.
