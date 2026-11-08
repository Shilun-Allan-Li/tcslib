<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_clr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of Register Clearing

**Claim.** If the instruction at $l$ clears register $r$ and the binary word for its initial value has length at most $W$, then the compiled program reaches the configuration at $l'$ with register $r$ set to zero, all other registers and the output unchanged, and all earlier configurations ordinary with every work-head position between $-1$ and $W$.

**Proof.** First express the initial configuration as a register configuration whose selected tape stores the binary word for $v(r)$ and whose head is at zero (`aseam_eq_regCfg`). The compiled transition and call descriptions (`armProg_tr`, `armProg_call`), together with the instruction hypothesis, allow the clearing-run result (`clr_run`) to be applied: it gives a finite run ending with the selected tape storing the binary word for zero and with head at zero. Translating that endpoint back to the original configuration identifies it with the required configuration at $l'$ with register $r$ updated to zero (`regCfg_aseam`). For each earlier time, `clr_run` supplies an ordinary state and a selected-head position $q$ with $-1\le q\le |\mathrm{bits}(v(r))|$. The assumed length bound gives $q\le W$, so the intermediate register-configuration criterion (`mid_regCfg`) yields the required simulation condition. The same length bound and $W\ge0$ supply the nonnegativity condition needed there.

**Key facts.** `Complexity.LogProg.armProg_tr`, `Complexity.LogProg.armProg_call`, `Complexity.LogProg.clr_run`, `Complexity.LogProg.aseam_eq_regCfg`, `Complexity.LogProg.regCfg_aseam`, `Complexity.LogProg.mid_regCfg`.
