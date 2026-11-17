<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_ret -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return-instruction halting behavior

**Claim.** If the instruction at $l$ returns $b$, the compiled program reaches a halting configuration with output equal to the initial output followed by $b$, all register heads in $[-1,W]$, and no earlier call state or head-position bound violation.

**Proof.** The compiled program has no call at $(l,\mathrm{start})$, since the instruction is a return (`armProg_call`). Its transition at that state is the return action, which emits $b$ and halts (`armProg_tr`); applying this action to the initial configuration leaves the input head, register tapes, and register heads unchanged and appends $b$ to the output. Consequently the run reaches the required configuration after one step (`rrun_one`, `rstep_noncall`). The final head-position bounds follow because the heads remain at zero and $0\le W$. There is only one earlier time, namely time zero (`rrun_zero`): there the machine is at $(l,\mathrm{start})$, where it has no call, and the register heads are again zero, hence in $[-1,W]$.

**Key facts.** `Complexity.LogProg.armProg_call`, `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`, `Complexity.LogProg.armProg_tr`, `Complexity.LogProg.rrun_zero`.
