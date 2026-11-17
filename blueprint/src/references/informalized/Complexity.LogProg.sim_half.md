<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register halving simulation

**Claim.** If the instruction at $l$ replaces register $r$ by $\lfloor v(r)/2\rfloor$ and continues at $l'$, then the compiled program reaches the configuration with that register updated, all other registers and the output unchanged, while earlier configurations have no pending oracle call and head positions stay in $[-1,W]$.

**Proof.** The halving-run lemma (`Complexity.LogProg.half_run`) supplies a finite run for the compiled halving instruction. Starting with the head on the binary word for $v(r)$ at cell $0$, it reaches the configuration whose tape contains the binary word for $v(r)/2$. At every earlier time, it provides a control phase with no pending oracle call and a head position between $-1$ and the length of the input binary word. The hypothesis identifying the instruction at $l$ with halving ensures the compiled transitions and call status match those required by the run. The starting `aseam` is the required register configuration by `Complexity.LogProg.aseam_eq_regCfg`, and the endpoint becomes the updated `aseam` by `Complexity.LogProg.regCfg_aseam`. Applying `Complexity.LogProg.mid_regCfg` to each earlier configuration gives the required call-free and head-position properties: its position bounds follow from the run bound and the assumed inequality with $W$. The binary-word length is nonnegative and bounded by $W$, so $W\ge0$, as needed there.

**Key facts.** `Complexity.LogProg.half_run`, `Complexity.LogProg.aseam_eq_regCfg`, `Complexity.LogProg.regCfg_aseam`, `Complexity.LogProg.mid_regCfg`.
