<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.step_x -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step input movement

**Claim.** If every possible work-tape reading makes the transition from $s$ on the symbol at $ip$ move the input head by $mvI$, leave the work tape unchanged, and enter $s'$, then one step sends the specified configuration to the corresponding configuration with moved input head and unchanged tape and work-head position.

**Proof.** First express the starting configuration as an updated view of itself using the configuration-update identity (`xCfg_K`). Since the program has no call at state $s$, the one-step run is given by the ordinary transition applied to this configuration (`rrun_one_x`). The hypothesis identifies that transition, for the actual work-tape reading in particular, with the action that moves only the input head and changes the state to $s'$. Applying this action's effect on an updated configuration (`apply_xAct`) leaves the tape unchanged and adds zero to the work-head position. The result is the claimed configuration, with the input position moved according to the clamped movement and the tape still storing the binary expansion of $v$; the same configuration-update identity identifies its form as $K$.

**Key facts.** `Complexity.LogProg.Dbl.xCfg_K`, `Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.apply_xAct`.
