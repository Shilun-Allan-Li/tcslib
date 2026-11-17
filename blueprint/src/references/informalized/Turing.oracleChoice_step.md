<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleChoice_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Choice Simulation

**Claim.** Outside the query state, the constructed deterministic machine's step simulates the nondeterministic machine's step using the bit scanned on the added tape, and advances that tape's head by one.

**Proof.** The added tape's scanned symbol is $b$, while the other work tapes, when read through the embedding that skips the choice-tape slot, give exactly the symbols read in $c$. Since the state is not the query state, both machines use their ordinary transition functions rather than submitting an oracle query. Thus the constructed machine applies the action of $N$ at state $q$ with choice bit $b$. That action is embedded into the larger configuration: it preserves the original tapes, input position, and output behavior, while the added tape is unchanged and its head advances from $p$ to $p+1$. The action-application identity `oracleChoiceAction_apply` yields precisely the asserted configuration.

**Key facts.** `Turing.oracleChoiceAction_apply`.
