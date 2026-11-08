<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLoad_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completed Loader State Is Fixed

**Claim.** Whenever the row loader’s control is the final field index paired with the fresh loader’s initial reset control, one machine step leaves the configuration unchanged.

**Proof.** At the final field index, the transition test for an index below $l$ fails, since that index has value $l$. The loader therefore takes its control-only action with zero input movement, no tape writes, and no head movement, while retaining the same control state. A control-only action of this kind changes at most the state and input position; its application leaves all other configuration components unchanged (`controlAction_apply`). Zero movement preserves the input position (`moveInputPos_zero`), and the chosen successor state is the same final control. Thus every component of the configuration is fixed.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
