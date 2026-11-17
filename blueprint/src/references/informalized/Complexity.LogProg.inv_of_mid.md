<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean :: Complexity.LogProg.inv_of_mid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant at Call-Free Configurations

**Claim.** If a configuration has no active oracle-call state and all register heads lie between $-1$ and $W$, then it satisfies the stated invariant.

**Proof.** Unfolding the invariant, its first clause is exactly the head-position bound in the hypothesis. For the call conditions, suppose a label is active and its call specification is present. The no-call hypothesis says that the program’s call map at this active label is `none`, contradicting the assumed presence of a call specification. Thus there are no active calls requiring verification, so the call-condition clause holds vacuously.
