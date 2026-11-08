<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_inc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register increment simulation

**Claim.** If the instruction at $l$ increments register $r$ and continues at $l'$, then the compiled program reaches the configuration with $r$ replaced by $v(r)+1$, all other registers and the output unchanged, while earlier configurations have no pending oracle call and head positions stay in $[-1,W]$.

**Proof.** The increment-run lemma (`Complexity.LogProg.inc_run`) supplies a finite run that starts with the binary word for $v(r)$ under the head at cell $0$ and ends with the binary word for $v(r)+1$. At every earlier time, the control is in one of the two increment phases, there is no pending oracle call, and the head position is between $-1$ and the length of the binary word for $v(r)+1$. The hypothesis that the instruction at $l$ is this increment identifies the compiled program's transitions and call status with those required by the run. Convert the starting `aseam` to the register configuration using `Complexity.LogProg.aseam_eq_regCfg`, and identify the endpoint with the updated `aseam` using `Complexity.LogProg.regCfg_aseam`. At each earlier time, the run lemma supplies the phase and bounds; the two possible phases have no pending call in the compiled program, and `Complexity.LogProg.mid_regCfg` turns the position bounds into the required property. The assumed bound on the output word length gives the needed upper bound $W$, and its nonnegative length also implies $W\ge0$.

**Key facts.** `Complexity.LogProg.inc_run`, `Complexity.LogProg.aseam_eq_regCfg`, `Complexity.LogProg.regCfg_aseam`, `Complexity.LogProg.mid_regCfg`.
