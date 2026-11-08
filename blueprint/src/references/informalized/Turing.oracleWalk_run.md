<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleWalk_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Walk Run

**Claim.** Under the stipulated transition behavior at each step before time $t$, after every $u\le t$ steps the first two heads are at $p+mu$, the other two heads remain fixed, and the configuration otherwise has the prescribed walk form.

**Proof.** Induct on the number of steps $u$, maintaining the assertion for every $u\le t$. At zero steps, the initial walk configuration has both designated heads at $p$, as required. For the successor step, use the run recurrence to obtain the next configuration by applying the machine's transition to the configuration at time $u$. The induction hypothesis identifies that configuration with the walk configuration at position $p+mu$, and the hypothesis on the transition row applies because $u<t$. That transition makes no writes, moves the first two heads by $m$, leaves the other heads stationary, and keeps the state $q$. The input head also remains fixed because its movement is zero (`moveInputPos_zero`); the output remains unchanged because no symbol is emitted. The new head location is $p+mu+m=p+m(u+1)$, so the resulting configuration is the required walk configuration. The run recurrence used here is `MultiTapeTM.runFrom_succ_eq_step'`.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.moveInputPos_zero`.
