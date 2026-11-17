<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleChoice_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial configuration with an oracle choice tape

**Claim.** The constructed machine's initial configuration, with the ordinary tapes blank and the added tape storing $u$, is the configuration obtained from the original machine's initial configuration by adjoining that tape with head at cell zero.

**Proof.** The two configurations have the same initial state, input-head position, and empty output. For work-tape contents, separate the added slot from the original slots: at the added slot the updated word assignment stores $u$, and at each other slot it stores the empty word, just as adjoining the buffer tape does. For head positions, every tape on both sides starts at zero, including the added tape. Thus all configuration fields agree.
