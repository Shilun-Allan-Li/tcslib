<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.runFrom_eq_plainEmptyOracle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement before an Oracle Query

**Claim.** If the plain simulation using the empty oracle never reaches the query state during the first $t$ configurations, then its configuration after $t$ steps agrees with the configuration of the oracle machine using $O$.

**Proof.** First identify the plain empty-oracle run with the oracle machine's run using the empty language, via the empty-oracle simulation theorem (`Turing.OracleTM.runFrom_plainEmptyOracle`). The hypothesis therefore says that this oracle run is never in the query state at any time $s<t$. The theorem that runs with two oracles agree whenever the first run avoids the query state (`Turing.OracleTM.runFrom_eq_of_forall_ne_qQuery`) now gives equality at time $t$ between the empty-language run and the run using $O$. Rewriting the former back as the plain simulation and reversing the equality yields the claim.

**Key facts.** `Turing.OracleTM.runFrom_plainEmptyOracle`, `Turing.OracleTM.runFrom_eq_of_forall_ne_qQuery`.
