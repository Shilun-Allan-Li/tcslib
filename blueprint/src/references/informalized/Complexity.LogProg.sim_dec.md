<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_dec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register decrement simulation

**Claim.** If the instruction at $l$ decrements register $r$ and continues at $l'$, then the compiled program reaches the configuration with $r$ replaced by $v(r)-1$, all other registers and the output unchanged, while earlier configurations have no pending oracle call and head positions stay in $[-1,W]$.

**Proof.** The decrement-run lemma (`Complexity.LogProg.dec_run`) supplies a finite run for the compiled decrement instruction, starting with the head on the binary word for $v(r)$ at cell $0$. It reaches the corresponding configuration whose tape contains the binary word for $v(r)-1$, and at every earlier time the control is in one of the decrement phases, no oracle call is pending, and the head position lies between $-1$ and the length of the original binary word. The hypotheses identifying the instruction at $l$ with a decrement make the compiled program's transitions and call status exactly those required by this run. The initial configuration `aseam` is the relevant register configuration by `Complexity.LogProg.aseam_eq_regCfg`; the endpoint is the stated updated `aseam` by `Complexity.LogProg.regCfg_aseam`. For each earlier configuration, the run lemma gives its phase, tape, and head position. The call-free condition is preserved by the compiled-program transition and call descriptions, and the head bound follows by combining the run's bound with the assumed binary-word-length bound $W$. Since that length is nonnegative and at most $W$, $W$ is nonnegative, as required for the midpoint bound.

**Key facts.** `Complexity.LogProg.dec_run`, `Complexity.LogProg.aseam_eq_regCfg`, `Complexity.LogProg.regCfg_aseam`, `Complexity.LogProg.mid_regCfg`.
