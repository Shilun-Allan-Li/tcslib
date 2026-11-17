<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_run_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Runs

**Claim.** If machines $A$ and $B$ take the same one-step transition from every configuration reached by $A$ at times $i<t$, then they reach the same configuration after $t$ steps from the same starting configuration.

**Proof.** Prove by induction on $i$ the stronger statement that the machines agree after every $i\le t$ steps. At $i=0$, both runs are at the starting configuration. For the successor step, assume they agree at time $i$ and $i+1\le t$. The run after $i+1$ steps is obtained by applying one step to the configuration at time $i$ (`runFrom_succ_eq_step'`). The induction hypothesis identifies the current configurations, and the assumed one-step agreement identifies the next configurations; hence the runs agree at time $i+1$. Taking $i=t$ gives the result.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
