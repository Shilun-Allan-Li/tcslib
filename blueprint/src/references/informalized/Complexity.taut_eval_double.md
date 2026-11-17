<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_eval_double -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Evaluation of a Doubled Bit

**Claim.** Under the given input-bit and transition hypotheses, two verifier steps consume two input positions and enter the specified control state, preserving the work word and shifting the work head by the prescribed sign.

**Proof.** In the first step, the input-reading property of the configuration (`Complexity.taut_read`) and the hypothesis that the bit at index $i$ is $b$ make the verifier read $b$. Its first-stage transition advances the input head without moving the work head and enters the intermediate state recording $b$; the configuration update is captured by the one-step movement fact (`Complexity.taut_move_right`). In the second step, the recorded bit and the work-tape reading determine the evaluation action. By hypothesis, that action is exactly the silent move to $q'$ with work-head movement $e$. Applying the same movement fact advances the input head once more and changes the work-head position from $h$ to $h+e$, leaving the stored word unchanged. The two run-successor identities and the zero-step run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`) identify these consecutive transitions with the claimed two-step run. The bound $i+2\le |x|$ ensures both input-head advances are valid.

**Key facts.** `Complexity.taut_read`, `Complexity.taut_move_right`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
