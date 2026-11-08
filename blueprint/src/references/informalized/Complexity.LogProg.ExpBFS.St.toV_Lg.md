<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.toV_Lg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm-Bound Coordinate

**Claim.** For every state $S$, the logarithm-bound coordinate of its 17-entry register vector is $S.Lg$.

**Proof.** The vector lists the state fields in order, with $S.Lg$ in position $1$. Since the logarithm-bound coordinate is indexed by that position, evaluating the vector there returns $S.Lg$ by its definition.
