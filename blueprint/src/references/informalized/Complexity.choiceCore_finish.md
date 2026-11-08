<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.choiceCore_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Choice-Core Verdict

**Claim.** After one step from the encoded configuration with choice-head position $|u|$, the core is halted and outputs $[1]$ exactly when the encoded configuration is halted and its output is $[1]$.

**Proof.** The choice head is positioned at $|u|$, beyond the last bit of the choice word, so the encoded choice-tape symbol there is absent. The core therefore takes its end-of-choice transition: it enters the halting state and emits the Boolean value of the condition that the simulated state is halted and the stored output summary is `some true`. By the characterization of the summary (`capturedSummary_true`), that summary is `some true` exactly when the simulated output is the one-bit word $[1]$. Thus the transition emits precisely the claimed verdict.

**Key facts.** `Complexity.capturedSummary_true`.
