<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleInstallCall -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-Time Oracle Call Implementation

**Claim.** A decider for the language can be converted into a finite Boolean machine with at least one work tape that writes the membership bit on tape 0, reaches its exit state for the first time after a positive number of steps, and obeys the stated linear bound.

**Proof.** First use the call-machine construction (`Turing.FinTM.exists_installCallTM`) with the function sending each word $z$ to the singleton list containing its membership bit. The decision-time hypothesis gives the required time bound for this function, and the construction supplies a machine, entry and exit states, a positive number of tapes, and a run that produces the desired singleton output. Its bound has the additional output-length cost, which here is one and is absorbed by the stated summand $|z|+2$.

If the constructed entry and exit states differ, use this machine directly. Its run is positive, and the construction’s first-exit condition at positive intermediate times, together with entry-state inequality at time zero, shows the exit state was not reached earlier.

If the states coincide, replace the machine by the seam-release construction, adjoining a fresh entry state and using the old entry as the exit. The first-return property of this construction (`Turing.seamReleaseTM_firstReturn`) preserves the output and time while ensuring the new exit is first reached at the terminal step. In either case the number of tapes and the time bound are retained.

**Key facts.** `Turing.FinTM.exists_installCallTM`, `Turing.seamReleaseTM_firstReturn`.
