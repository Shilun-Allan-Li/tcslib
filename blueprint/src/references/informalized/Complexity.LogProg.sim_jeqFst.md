<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_jeqFst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-component equality simulation

**Claim.** On a valid nested pair input, the compiled program reaches the successor determined by whether the register's binary expansion equals the first inner component, preserving the input, valuation, and output; throughout the preceding run, no call is pending and all work-head positions lie in $[-1,W]$.

**Proof.** Use validity of the input to write it as the encoding of a unary prefix followed by an inner pair with components $u$ and $w$. The first-component run lemma (`Complexity.LogProg.jeqPairFst_run`) applies to the compiled transition behavior at the phases for this test: it gives a finite run whose branch is positive exactly when $u$ equals the register's binary word, and bounds every intermediate head position below by $-1$ and above by that word's length; it also ensures that no call is pending. The program transition and call identities (`Complexity.LogProg.armProg_tr` and `Complexity.LogProg.armProg_call`) verify the required phase behavior and absence of calls. The decoding identity for valid pair encodings (`Complexity.LogProg.pairWords_pairEncode`) identifies the first component returned by `pairWords` with $u$. Reorienting the equality in the run's branch condition gives the stated successor condition. Finally, the configuration identities `Complexity.LogProg.xCfg_aseam_self` and `Complexity.LogProg.xCfg_aseam` identify the run's starting and ending configurations with the desired seam configurations, and the reachability-to-simulation result (`Complexity.LogProg.simTo_of_reachesB`) converts the bounded run into `SimTo`. The assumed length bound supplies its upper-bound hypothesis.

**Key facts.** `Complexity.LogProg.jeqPairFst_run`, `Complexity.LogProg.pairWords_pairEncode`, `Complexity.LogProg.simTo_of_reachesB`.
