<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.nastep_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A choice instruction selects its prescribed state

**Claim.** If the instruction at state $l$ chooses between $l_1$ and $l_0$, then one step with choice bit $b$ moves to $l_1$ when $b$ is true and to $l_0$ when $b$ is false, leaving the register valuation and result unchanged.

**Proof.** Substitute the assumed instruction at $l$ into the definition of the nondeterministic step. The choice branch updates only the control state, selecting $l_1$ or $l_0$ according to $b$; the register valuation and result are carried through unchanged.
