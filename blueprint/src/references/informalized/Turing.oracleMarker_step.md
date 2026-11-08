<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleMarker_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Marker Update Step

**Claim.** If the dispatch transition has the specified stationary input and tape action, then one step from the given configuration yields the local configuration with state $q'$.

**Proof.** Apply the general one-step rule for an action that writes a symbol on one tape (`Turing.step_of_tapeAction_write`). The assumed transition writes the current value of the oracle-origin tape at the first two heads’ shared position $p$ onto tape 1, leaves that head stationary, and changes the state to $q'$. The input movement is zero, so the input-head position is unchanged (`Turing.moveInputPos_zero`). The updated tape 1 is therefore its previous content—the bookmark marker at $p$—overwritten by the origin-tape value at $p$; the other tapes and heads remain unchanged. Comparing each tape cell and each head position gives precisely the local configuration.

**Key facts.** `Turing.step_of_tapeAction_write`, `Turing.moveInputPos_zero`.
