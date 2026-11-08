<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRow_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idle End-of-Row State

**Claim.** Whenever the row controller is at the end-of-row index with copier control $0$, one step leaves the entire configuration unchanged.

**Proof.** At the end-of-row index, the field index is not less than $l$. The row machine therefore takes its end-of-row transition, which is a control-only action with zero input movement, no work-tape writes or head movements, no output, and the same state. A zero input movement leaves the input position fixed (`moveInputPos_zero`); since all other configuration components are also unchanged, the whole configuration is fixed.

**Key facts.** `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
