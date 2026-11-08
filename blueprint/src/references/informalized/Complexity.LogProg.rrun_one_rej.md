<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.rrun_one_rej -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Rejection Behavior

**Claim.** Under the stated no-call and rejection-transition hypotheses, the run from the specified input configuration halts after one step, appends false to the output, and has the specified register-head positions.

**Proof.** The one-step result for an input configuration identifies the run with the prescribed transition applied to that configuration (\texttt{Complexity.LogProg.rrun_one_x}). The transition hypothesis says that this action is the rejection action for every scanned work-symbol tuple, so it applies in particular to the tuple scanned in the given configuration. The rejection action halts, emits false, and leaves all work-head positions fixed. The initial configuration has the head positions of $c$ except that register $r$ is at $p$; applying the action therefore gives the stated state, output, and head positions.

**Key facts.** `Complexity.LogProg.rrun_one_x`.
