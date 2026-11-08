<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Lockstep.locate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Locating a Simulated Configuration

**Claim.** Every time up to the accumulated simulation cost can be represented as a run from the encoding of some original configuration at a time $u\le t$, using either zero steps or at most that configuration's simulation cost.

**Proof.** Induct on $t$. When $t=0$, the total cost is zero, so the only allowed time is zero; choose $u=0$ and $w=0$. For the successor case, split the total cost into the earlier partial sum and the cost at time $t$. If $v$ is at most the earlier partial sum, apply the induction hypothesis using the inherited avoidance assumption, and retain its configuration time and offset. Otherwise, write $v$ as the earlier partial sum plus an offset $w$. Choose $u=t$; the offset is positive and no greater than the cost at time $t$, and the assumed avoidance condition applies at time $t$. By the lockstep run identity (`runFrom`), the simulated run at the earlier partial sum is the encoding of the original configuration at time $t$. The run-addition law (`runFrom_add`) then shows that continuing for $w$ steps gives exactly the simulated configuration at time $v$.

**Key facts.** `Turing.Lockstep.runFrom`, `Turing.MultiTapeTM.runFrom_add`.
