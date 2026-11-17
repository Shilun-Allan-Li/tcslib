<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_Eval_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Administrative Interpreter Step

**Claim.** Under the stated transition hypothesis, one interpreter step produces the evaluation configuration with the target control, moved cursors, and the specified state-tape update.

**Proof.** The current evaluation configuration reads exactly the four symbols displayed in the hypothesis: the table-buffer symbol at $p$, the state-tape symbol at $s$, and the base configuration’s reads on tapes 2 and 3. This is the work-read identity (`Turing.timedCut_Eval_reads`). The transition hypothesis then identifies the interpreter’s action on those reads as the stated administrative action. Applying that action to the evaluation configuration gives the target control, table cursor $p+d_t$, state cursor $s+d_s$, and the state tape left unchanged or updated at $s$ according to the optional write (`Turing.timedCut_Admin_apply`). Since the current control is active, the interpreter step is exactly the transition action applied to the current configuration, proving the result.

**Key facts.** `Turing.timedCut_Eval_reads`, `Turing.timedCut_Admin_apply`.
