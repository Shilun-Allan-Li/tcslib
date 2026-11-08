<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.FinOracleNDTM.exists_choiceTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic simulation of choice output

**Claim.** For every finite-state nondeterministic oracle machine, there is a finite-state deterministic oracle machine and an ordinary work-tape index such that, for every oracle, input, and choice word, its run for $2|u|+2$ steps halts and outputs the choice output assigned to the nondeterministic machine.

**Proof.** Choose the deterministic oracle machine constructed as the choice simulator for $N$, and designate its last ordinary work tape as the tape holding $u$. The initialization identity (`oracleChoice_initial`) identifies this machine's initial configuration, with $u$ stored on that tape, with the simulator configuration used in the simulation argument. The simulation result (`oracleChoice_run`) gives a time $s\leq 2|u|+2$ at which the simulator has halted and its output equals the nondeterministic machine's choice output (including the prescribed false bit when that run has not halted). To extend this conclusion to exactly $2|u|+2$ steps, write that time as $s+(2|u|+2-s)$. The iteration law for deterministic runs (`runFrom_add`) splits the run at time $s$; because the configuration then has halted state, all remaining steps leave it unchanged (`runFrom_of_halt`). The run at the stated time therefore remains halted with the required output.

**Key facts.** `Turing.oracleChoice_initial`, `Turing.oracleChoice_run`, `Turing.OracleTM.runFrom_add`, `Turing.OracleTM.runFrom_of_halt`.
