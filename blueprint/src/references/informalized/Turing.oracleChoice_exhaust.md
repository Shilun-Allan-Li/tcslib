<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleChoice_exhaust -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting of the oracle choice machine

**Claim.** From the configuration obtained by adding the tape with its head at a blank cell, the oracle choice machine halts within two steps, with output equal to the original output if the starting configuration was halted and otherwise the original output followed by false.

**Proof.** The added tape is blank at the head in the enlarged configuration by the assumption that $tape(p)=\mathrm{none}$. Split according to whether the original configuration is already halted. If its state is none, the enlarged configuration is also halted, so zero steps suffice; its output is unchanged. Otherwise write its state as $q$. If $q$ is the query state, the first step performs the oracle answer transition, changing the state to one of the answer states and leaving the tape blank at its head. The blank-transition result then applies on the next step, halting and appending false. The query transition is given by the query-state rule (`OracleTM.step_of_qQuery`). If $q$ is not the query state, the blank-transition result applies immediately, so one step suffices. In both nonhalted cases the output is the original output followed by false, and the exhibited step count is at most two.

**Key facts.** `Turing.OracleTM.step_of_qQuery`, `Turing.oracleChoice_blank`.
