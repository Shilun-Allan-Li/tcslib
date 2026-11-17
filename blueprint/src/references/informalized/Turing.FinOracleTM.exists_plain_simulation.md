<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.FinOracleTM.exists_plain_simulation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of an oracle computation

**Claim.** Given an oracle machine $M$ and a machine $D$ deciding its oracle language, there are a finite ordinary machine $P$ with at least $k+1$ work tapes and a constant $a$ such that every halting run of $M$ from the specified initial configuration is simulated by $P$ with the same output, within the stated bound involving the query costs $q_r$.

**Proof.** The proof first obtains from the oracle-installation result a finite machine $C$ that can run the decider $D$ on a query and return its yes-or-no answer, with the stated cost bound (\texttt{Turing.oracleInstallCall}). It then builds an oracle host that incorporates this query procedure alongside a simulation of $M$. The host simulation result gives, for each halting run of $M$, a time $s$ within the claimed bound at which the host has halted with the same output (\texttt{Turing.oracleHost_run}). This host has at least the required number of tapes by its construction. The proof then selects the host's first halting time $u\le s$ (\texttt{Turing.MultiTapeTM.exists_first_halt}). Since a halting configuration stays fixed under subsequent steps, the configuration at $u$ equals that at $s$; hence it is halted and has the same output as the original run. The bound for $s$ also bounds $u$.

**Key facts.** `Turing.oracleInstallCall`, `Turing.oracleHost_run`, `Turing.MultiTapeTM.exists_first_halt`.
