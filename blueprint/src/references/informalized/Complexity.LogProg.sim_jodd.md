<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.sim_jodd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oddness-test simulation

**Claim.** The compiled program reaches the successor state selected by whether register $r$ is odd, without visiting a call state beforehand and with every register head position in $[-1,W]$.

**Proof.** Apply the general one-step simulation result (`sim_go`) with the target state chosen according to the parity of $v(r)$. The call-state condition follows because an oddness instruction at phase `start` has no call specification (`armProg_call`). For the transition condition, the compiled transition agrees with the instruction transition (`armProg_tr`): it branches to the positive successor exactly when the current tape symbol is `some true`. At head position zero, the buffered tape symbol is the first bit of `Nat.bits (v r)`. The fact that this first bit records oddness (`bits_head_odd`) therefore identifies the branch. Splitting first on whether $v(r)=0$, and then on whether its remainder modulo $2$ is $1$, verifies that this branch agrees with the chosen target in every case. The bound on head positions and the absence of calls during the run are then supplied by `sim_go`.

**Key facts.** `Complexity.LogProg.sim_go`, `Complexity.LogProg.armProg_call`, `Complexity.LogProg.armProg_tr`, `Complexity.LogProg.bits_head_odd`.
