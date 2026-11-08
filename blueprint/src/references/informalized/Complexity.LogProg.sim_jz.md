<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_jz -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-test simulation

**Claim.** The compiled program reaches the successor state selected by whether register $r$ is zero, without visiting a call state beforehand and with every register head position in $[-1,W]$.

**Proof.** Apply the general one-step simulation result (`sim_go`) with the target state chosen according to whether $v(r)=0$. The compiled program has no call at this instruction and phase (`armProg_call`). Its transition at phase `start` implements the zero test (`armProg_tr`): it selects the positive successor precisely when the current tape symbol is absent. At head position zero, the symbol on register $r$ is the first bit of its binary word in the buffer tape; the first-bit description (`bits_head_odd`) says this symbol is absent exactly when the number is zero. Thus the transition is the required branch, and `sim_go` supplies the stated reachability and intermediate head-position bounds.

**Key facts.** `Complexity.LogProg.sim_go`, `Complexity.LogProg.armProg_call`, `Complexity.LogProg.armProg_tr`, `Complexity.LogProg.bits_head_odd`.
