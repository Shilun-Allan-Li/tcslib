<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.xCfg_K -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration update for the doubled machine

**Claim.** Updating the state, input-head position, and work-tape head position of the specified configuration yields the configuration with those updated values, the same binary tape, and empty output.

**Proof.** Unfold the configuration update and the definition of the doubled machine's configuration. The state, input position, tape, and output agree immediately. For the work-head positions, there is only one tape, so its index is $0$; updating that entry to $q$ gives the constant head-position function with value $q$. The two configurations therefore agree in every component.
