<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleChoice_blank -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Blank oracle-choice transition

**Claim.** When the machine is outside its query state and the added choice tape is blank at its head, one step halts, leaves the tapes and head positions unchanged, and appends false to the output.

**Proof.** Because the state is not the query state, the oracle machine uses its ordinary transition function. The constructed machine's rule first inspects the added tape; since its scanned cell is blank, it selects the action that writes nothing, moves no head, outputs false, and has no successor state. Applying this action preserves every tape, leaves each work-tape head fixed, and leaves the input-head position fixed by the zero-movement identity (`moveInputPos_zero`). The output is extended by the one-symbol list containing false. These are exactly the fields of the asserted halting configuration.

**Key facts.** `Turing.moveInputPos_zero`.
