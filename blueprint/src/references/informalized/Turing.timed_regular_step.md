<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_regular_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Regular-State Replay Step

**Claim.** If the table interpreter configuration is live and its control is not an `applyRecord` state, one timed-interpreter step from its lift with clock word $w$ equals the lift, with the same clock word, of one stopped table-interpreter step.

**Proof.** Write the live control of the original configuration as $q$. The lift preserves the input symbol and the symbols under the four original work-tape heads, so the universal interpreter sees the same data in both configurations. Since $q$ is not an `applyRecord` control, the timed interpreter's transition in control `work $q$` is exactly the timed version of the universal interpreter's transition. The timed-action lifting identity (`timedAction_apply`) then shows that applying this transition to the lifted configuration gives the lift of the result of that universal transition, with the clock unchanged. Finally, away from `applyRecord` controls, the stopped interpreter's transition agrees with the universal interpreter's transition (`timedCut_regular`). Combining these identities gives the claimed one-step equality.

**Key facts.** `Turing.timedAction_apply`, `Turing.timedCut_regular`.
