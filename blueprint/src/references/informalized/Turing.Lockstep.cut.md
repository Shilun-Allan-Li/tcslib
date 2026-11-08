<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Lockstep.cut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Avoidance Before Accumulated Cost

**Claim.** If the original run avoids $X$ through the first $t$ configurations, then the simulated run avoids $X'$ at every time strictly before the sum of their simulation costs.

**Proof.** Induct on $t$. At $t=0$, the accumulated cost is zero, so there is no natural number strictly below it. For the successor case, write the accumulated cost as the sum through time $t-1$ plus the cost of the configuration at time $t$. Given a time $v$ below this total, first check whether it is below the earlier partial sum. If so, the induction hypothesis applies, since the avoidance assumption still holds for all times before $t$. Otherwise, express $v$ as the earlier partial sum plus some offset $w$. The lockstep run identity (`runFrom`) identifies the simulated configuration at the earlier partial sum with the encoding of the original configuration at time $t$. The run-addition law (`runFrom_add`) then identifies the simulated configuration at time $v$ with the run from that encoding for $w$ steps. The offset is strictly less than the cost at time $t$, so the lockstep interior-avoidance hypothesis gives that its state lies outside $X'$.

**Key facts.** `Turing.Lockstep.runFrom`, `Turing.MultiTapeTM.runFrom_add`.
