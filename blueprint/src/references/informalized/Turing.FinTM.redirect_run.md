<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.FinTM.redirect_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run correspondence under redirection

**Claim.** After $t$ steps from its initial configuration on $x$, the redirected machine is in the redirected image of the configuration reached by $M$ after $t$ steps from its own initial configuration on $x$.

**Proof.** The initial configuration of the redirected machine is the redirected image of the original initial configuration. Moreover, the one-step correspondence lemma says that taking one redirected step from the redirected image of any original configuration gives the redirected image of the original machine's next configuration (`redirect_step`). Applying the general iteration principle for maps that commute with one-step evolution (`runFrom_comm_of_step`) propagates this correspondence through every number $t$ of steps.

**Key facts.** `Turing.FinTM.redirect_step`, `Turing.MultiTapeTM.runFrom_comm_of_step`.
