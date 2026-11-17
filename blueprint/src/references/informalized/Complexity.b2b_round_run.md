<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_round_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Round of the Boolean Computation

**Claim.** Under the stated simulation, space, and increment hypotheses, the round-body machine reaches the true-verdict configuration when $b$ is true, and otherwise returns to the test anchor with first tape $v$. The run has positive length, avoids both endpoint states at its intermediate times, and satisfies the stated work-head bound throughout.

**Proof.** First apply the test-run theorem (`Complexity.b2b_trial_run`). It gives a positive-length run from the test anchor to the verdict phase carrying $b$, with the specified output word on the second tape, and controls the head positions throughout. The phase-host theorem (`Turing.phaseHostTM_run`) identifies this test-phase run with the corresponding prefix of the round-body machine, provided no redirect occurs earlier. The test-run exclusion of the verdict state before its endpoint verifies that condition. If $b$ is true, this prefix ends at the desired true-verdict configuration, and its intermediate-state and head bounds give the claims. If $b$ is false, the phase host redirects after the verdict endpoint into the clearing phase. The rejecting-suffix theorem (`Complexity.b2b_reject_suffix`) then supplies a positive-length continuation that clears the second tape, increments the first tape from $u$ to $v$, and returns to the test anchor, with no earlier visit to either excluded state and with the required head bound. Concatenate the prefix and suffix using the run-addition identity (`Turing.MultiTapeTM.runFrom_add`). Before the redirect, use the test-run bounds and state exclusions; at the redirect time, the verdict is false and hence is neither excluded state; after it, use the suffix guarantees. The maximum head bound from the two segments is at most $|x|+|u|+s_V+s_I+1$, since each segment’s bound is no larger than this sum.

**Key facts.** `Complexity.b2b_trial_run`, `Turing.phaseHostTM_run`, `Complexity.b2b_reject_suffix`, `Turing.MultiTapeTM.runFrom_add`.
