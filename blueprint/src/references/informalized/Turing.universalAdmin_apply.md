<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalAdmin_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of an Interpreter Action

**Claim.** Applying the administrative action changes the interpreter control state, advances the table and state cursors by their prescribed movements, and performs the prescribed optional write on the state tape.

**Proof.** The administrative action leaves the input head and output unchanged, and its four work-tape instructions act separately on the table tape, state tape, and two untouched tapes. The input head stays fixed by the zero-movement identity (Turing.moveInputPos_zero). On the table tape, the action writes nothing and moves by $d_t$, so its cursor becomes $p+d_t$. On the state tape, it moves by $d_s$ and either leaves the contents unchanged or updates the cell at the old cursor $s$ with the prescribed bit or blank. The remaining tapes are neither written nor moved. These componentwise facts give exactly the stated evaluation configuration.

**Key facts.** `Turing.moveInputPos_zero`.
