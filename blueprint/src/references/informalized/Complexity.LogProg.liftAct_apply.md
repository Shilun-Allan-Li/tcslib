<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.liftAct_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extension of a machine action

**Claim.** Extending a configuration by one work tape with contents $M$ and head position $p$, and extending an action to leave that tape stationary and unwritten, commutes with applying the action: the result is the extension by $M,p$ of the original action's result.

**Proof.** Compare the two configurations field by field. The state, input-head position, and output agree because both sides apply the same original action to the original configuration. For work tapes and their head positions, split the tape index into the new final tape and an old tape, using the decomposition of indices in a finite extension. On the final tape, the extended action writes nothing and moves by zero, so its contents remain $M$ and its head remains at $p$. On every old tape, the appended tape component is absent, and the extended action agrees with the original action; thus both contents and head position are exactly those obtained by applying the original action.
