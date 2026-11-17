<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleChoice_pause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pause step on the choice tape

**Claim.** When the added tape scans $b$ and the control is in auxiliary state $r$, one step changes the underlying state to $q_{\mathrm{yes}}$ when $r=0$ and to $q_{\mathrm{no}}$ otherwise, and moves the added tape head from $p$ to $p+1$.

**Proof.** The state is an auxiliary state, not the machine's query state, so the ordinary transition rule is used. Since the added tape scans $b$, its transition selects the auxiliary-state action that writes nothing and outputs nothing, sets the original machine's state according to whether $r=0$, and leaves all original tapes and their head movements as prescribed by that action. The lifted-action calculation says that applying this action to the enlarged configuration yields the lift of the original action, preserving the added tape contents and advancing its head to $p+1$ (`oracleChoiceAction_apply`). The input head is unchanged because its movement is zero (`moveInputPos_zero`).

**Key facts.** `Turing.moveInputPos_zero`, `Turing.oracleChoiceAction_apply`.
