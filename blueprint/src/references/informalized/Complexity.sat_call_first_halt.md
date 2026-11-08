<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_call_first_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Halt in a Padded Run

**Claim.** If a nonhalted configuration reaches a halted configuration after $t$ steps, there is a first halting time $u$ with $0<u\le t$, and the configuration at time $u$ equals the one at time $t$.

**Proof.** Choose $u$ to be the least time at which the run is halted; such a time exists because time $t$ is one. By minimality, every earlier time $v<u$ is nonhalting, and $u\le t$. Also $u$ cannot be zero: the run at time zero is the starting configuration, which is nonhalted. To compare the configurations at times $u$ and $t$, split the run at time $u$ using the run composition law ( `runFrom_add` ). Since the configuration at time $u$ is halted, every further step leaves it unchanged ( `runFrom_of_halt` ). Thus the run at time $t$ equals the configuration at time $u$. The time-zero identity ( `runFrom_zero` ) identifies the initial run with the given starting configuration in the exclusion of $u=0$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.runFrom_zero`.
