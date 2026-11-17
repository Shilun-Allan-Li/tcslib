<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeCfg_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idle action on a bridge configuration

**Claim.** Applying the idle action with successor state $q'$ to a bridge configuration in state $q$ changes only its control state to $q'$. The input-head position, stack assignment, and output remain unchanged.

**Proof.** Compare the fields of the two configurations. The action explicitly sets the successor control state to $q'$. Its zero input movement leaves the input-head position fixed; it makes no writes or movements on any work tape, so every tape and tape-head position is unchanged; and it emits no symbol, so the output is unchanged. Thus all fields agree with the bridge configuration having state $q'$.
