<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_live_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Liveness of Run Prefixes

**Claim.** If a machine is still live after $t$ steps from a configuration, then it is live after every number $u\le t$ of steps from that configuration.

**Proof.** Fix $u\le t$ and suppose the configuration at time $u$ is halted. Since $t=u+(t-u)$, the run addition law says the configuration at time $t$ is obtained by running for $t-u$ more steps from the configuration at time $u$. A halted configuration remains unchanged under every further run, so the configurations at times $t$ and $u$ are equal. The configuration at time $u$ is halted by assumption, hence so is the one at time $t$, contradicting the assumed liveness there. Thus the configuration at time $u$ must be live.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
