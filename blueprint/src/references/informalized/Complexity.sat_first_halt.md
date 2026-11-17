<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_first_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Halting Time

**Claim.** If a finite Turing machine computes $y$ from $x$ within $T$ steps, then some time $t\le T$ is its first halting time, and its output at that time is $y$.

**Proof.** The computation hypothesis gives both that the run is halted at time $T$ and that its output there is $y$ ( `FinTM.computesInTime_iff` ). Choose the least halting time $t$; it exists since $T$ is a halting time. Minimality says the machine has not halted at any earlier time, and gives $t\le T$. Split the run at time $t$ using the run composition law ( `MultiTapeTM.runFrom_add` ). The run after time $t$ remains at that halted configuration ( `MultiTapeTM.runFrom_of_halt` ), so the configuration at time $T$ equals the one at time $t$. In particular, the output at time $t$ is the output $y$ at time $T$.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
