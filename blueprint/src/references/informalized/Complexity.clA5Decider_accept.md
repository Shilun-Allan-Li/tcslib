<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Decider_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance from the emitted verdict

**Claim.** If a finite Boolean machine halts by time $T$ and its output is the Boolean indicator of membership in $V$, then every step before time $T$ emits either no bit or true exactly when $y$ belongs to $V$.

**Proof.** The no-false-emission characterization (\texttt{clA5NoFalse}) identifies the condition that no step before $T$ emits false with the condition that the final output contains no false bit. The machine’s time-computation hypothesis supplies that final output as the one-element list containing the membership indicator (\texttt{computesInTime_iff}). If $y\in V$, the indicator is true, so the output list has no false bit and the no-false-emission condition holds. If $y\notin V$, the indicator is false, so the output contains false and that condition fails. This proves the equivalence.

**Key facts.** `Complexity.clA5NoFalse`, `Turing.FinTM.computesInTime_iff`.
