<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_release -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Releasing the Loop Body

**Claim.** From the startup call with a halted body configuration, release disabled, and false flag, one host step produces the corresponding non-startup call with the body state set to the anchor, release enabled, and blank flag, while preserving the other configuration data.

**Proof.** In the startup call state, the host delegates to its control action with no input movement, clears the flag tape, and sets the next state to the non-startup call carrying body state $(a,\mathrm{true})$. The body’s halted configuration contributes no ordinary body-state component to this transition; the host’s return state supplies the anchor and enables release. To identify the resulting configuration, compare its fields: the input head stays fixed because a zero movement leaves its position unchanged (`moveInputPos_zero`); the body tapes, payload, fuel tapes and their head positions are preserved; the flag becomes blank; and the output is unchanged. These fieldwise equalities give the stated call configuration.

**Key facts.** `Turing.moveInputPos_zero`.
