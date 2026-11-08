<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_jeqSnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-component equality simulation

**Claim.** On a valid nested pair input, the compiled program reaches the successor determined by whether the register's binary expansion equals the second inner component, preserving the input, valuation, and output; throughout the preceding run, no call is pending and all work-head positions lie in $[-1,W]$.

**Proof.** Validity presents the input as a unary prefix followed by an inner pair with components $u$ and $w$. The second-component run lemma (`Complexity.LogProg.jeqPairSnd_run`) follows the compiled phases that skip the prefix and first inner component, compare the register's binary word with $w$, and return to the initial head position. It provides a finite run branching according to equality with $w$, with no pending call at every earlier configuration and head position between $-1$ and the binary-word length. The compiled transition and call identities (`Complexity.LogProg.armProg_tr` and `Complexity.LogProg.armProg_call`) verify those phase transitions and the absence of calls. By the pair decoding identity (`Complexity.LogProg.pairWords_pairEncode`), the second component of `pairWords` on this input is $w$. Reversing the equality in the run's branch condition therefore gives the successor stated in the claim. The seam identities `Complexity.LogProg.xCfg_aseam_self` and `Complexity.LogProg.xCfg_aseam` identify the run endpoints with the desired configurations. Finally, `Complexity.LogProg.simTo_of_reachesB` turns this bounded run into the required simulation; the assumed binary-length bound ensures its head-position upper bound is at most $W$.

**Key facts.** `Complexity.LogProg.jeqPairSnd_run`, `Complexity.LogProg.pairWords_pairEncode`, `Complexity.LogProg.simTo_of_reachesB`.
