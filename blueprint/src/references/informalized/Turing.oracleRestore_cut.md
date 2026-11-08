<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleRestore_cut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoration Before Completion

**Claim.** At every time $u<|p|+3$, any state reached from the read configuration under the side condition satisfies the internal-state predicate, so it is not ready, copy, or an answer state.

**Proof.** For $u<3$, the integer time is one of $0,1,2$. At time zero the state is read; at time one it is restore with the indicated optional side; and at time two the restoration-at-the-bookmarked-cell result gives depart (`Turing.oracleRestore_cell`). Each is an internal state by the definition of the predicate. Otherwise $u\ge3$. The strict upper bound rules out $p=0$, so the three-step restoration result puts the machine in the back configuration at time three (`Turing.oracleRestore_three`). Split off those first three steps using run concatenation (`Turing.MultiTapeTM.runFrom_add`); the backward-run formula then shows that at the remaining time the state is still back (`Turing.oracleBack_run`). Back is internal as well. In each case, equality of the reached state with $q$ identifies $q$ with the state just described, proving the assertion.

**Key facts.** `Turing.oracleRestore_cell`, `Turing.oracleRestore_three`, `Turing.MultiTapeTM.runFrom_add`, `Turing.oracleBack_run`.
