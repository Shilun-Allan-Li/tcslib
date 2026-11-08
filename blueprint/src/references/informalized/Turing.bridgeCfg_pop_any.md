<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeCfg_pop_any -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pop a possibly empty bridge stack

**Claim.** For any stack at $k$, the specified action produces the bridge configuration with that stack replaced by its tail, moving the head right if the stack is nonempty and leaving it in place if the stack is empty; all other configuration data is preserved except the control state, which becomes $q'$.

**Proof.** Split on whether the stack at $k$ is empty. If it is empty, its tail is still empty, and the action chooses zero head movement. The bridge representation of an empty stack contains no symbols (`bridgeStack_nil`); the action's blank write therefore leaves that tape unchanged. The other tapes are untouched, and zero input movement fixes the input position (`moveInputPos_zero`). Thus only the state changes to $q'$. If the stack is nonempty, write it as $a::xs$. The conditional chooses a rightward movement, and the nonempty-stack pop result (`bridgeCfg_pop`) says this blanks the current cell and replaces the represented stack by $xs$. In either case, the output is unchanged because the action emits nothing, proving the claim.

**Key facts.** `Turing.bridgeStack_nil`, `Turing.moveInputPos_zero`, `Turing.bridgeCfg_pop`.
