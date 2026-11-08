<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.armProg_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Call Behavior of the Compiled Program

**Claim.** For every label $l$ and phase $ph$, the call specification of the register program compiled from $A$ with initial label $l_0$ equals the call specification obtained by applying the instruction $A(l)$ at phase $ph$.

**Proof.** Unfold the compiled program's call map: at the state $(l,ph)$ it is defined to be the call specification of $A(l)$ at phase $ph$. Thus the two sides are identical by the definitions.
