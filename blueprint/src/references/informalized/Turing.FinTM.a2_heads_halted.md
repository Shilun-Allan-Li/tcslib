<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_heads_halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head Bounds After Halting

**Claim.** If the run from $c$ has halted by time $a$, and all configurations through time $a$ have work-tape heads in $[-B,B]$, then the same bound holds at every time.

**Proof.** Fix a time $u$. If $u\le a$, the bound is the hypothesis. Otherwise write $u=a+(u-a)$. The run at time $a$ is halted, so the configuration at time $u$ equals the configuration at time $a$ (`runFrom_add` and `runFrom_of_halt`). Its heads therefore satisfy the assumed bound at time $a$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
