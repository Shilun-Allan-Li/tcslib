<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleReadyCfg_replace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replacing the Ready Argument

**Claim.** Replacing work tape $3$ of the ready configuration by the buffer storing a result word, and changing its state to $q'$, gives exactly the ready configuration with that result word and state.

**Proof.** Compare the configuration fields. The state becomes $q'$ by the specified replacement, while input position, tape-head positions, and output are unchanged. The first three work tapes of the ready configuration are independent of the argument word. Its fourth tape is the buffer of that argument; replacing this tape by the buffer of the result gives precisely the fourth tape in the ready configuration built with the result. Thus all fields agree.
