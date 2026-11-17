<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_trial_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded b2b Trial Run

**Claim.** Given the identity-machine computation and the cleaned verifier computation, the trial machine reaches the verdict state recording $b$ at a positive time, with the buffer and copied word in place. Before then it leaves the anchor phase, avoids every verdict state, never halts or emits output, and respects the stated work-head bound.

**Proof.** Decompose the run into its successive phases. The anchor phase takes one step and redirects to the identity phase. The identity capture lemma (`b2b_trial_capture`) gives a finite segment ending at the captured word $x$, with no premature exit and head positions bounded by $|x|+s_i$. The rewind lemma (`b2b_rewind_return`) then returns the input head to position $1$ without changing any work-head positions. The copy trial lemma (`b2b_trial_copy`) appends $u$ to $x$, reaches its done state only at the end of its segment, and bounds the heads by $|x|+|u|+1$. The call lemma (`b2b_trial_call`) runs the cleaned verifier on $x\mathbin{++}u$, captures its output $b$, and bounds the heads by $|x|+|u|+s_v+1$. Finally, the verdict trial lemma (`b2b_trial_verdict`) reads and erases the captured bit in two steps, reaching the verdict state recording $b$.

The phase-hosting lemma (`phaseHostTM_run`) joins each phase segment to its redirect step, provided the redirect state is not reached prematurely; the capture, rewind, copy, and call lemmas supply these guards. The proof records the cumulative phase boundaries and uses induction through those segments to cover every time up to the final time. This coverage shows that the anchor occurs only at time zero, no verdict state occurs before the final two-step verdict segment finishes, and the final time is positive. Each phase segment emits no output and does not halt; the resulting whole run therefore has empty output and remains nonhalting through the endpoint. The phasewise head bounds combine to the claimed global bound.

**Key facts.** `Complexity.b2b_trial_capture`, `Complexity.b2b_rewind_return`, `Complexity.b2b_trial_copy`, `Complexity.b2b_trial_call`, `Complexity.b2b_trial_verdict`, `Turing.phaseHostTM_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.output_prefix`.
