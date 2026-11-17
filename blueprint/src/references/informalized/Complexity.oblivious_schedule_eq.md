<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Snapshot.lean :: Complexity.oblivious_schedule_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oblivious head schedule

**Claim.** For an oblivious finite-state Turing machine, after $t$ steps on a binary input $x$, the input-head position and the tuple of work-tape head positions agree with those after $t$ steps on the all-zero input of length $|x|$.

**Proof.** Apply obliviousness to the two inputs $x$ and the list of $|x|$ zeros. They have the same length, so the definition of obliviousness gives equality of the input-head positions and of the work-tape head-position tuples after $t$ steps. By definition, those positions on the all-zero input are the schedules in the claim.
