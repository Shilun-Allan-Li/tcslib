<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_tables_coincide -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice Independence Outside Guessing States

**Claim.** At every reverse-host state other than a live scheduler state, the transition action is independent of the choice bit, for every input symbol and work-tape contents.

**Proof.** The host state has three disjoint forms: a loader state, a scheduler-state option, or a verifier-state tuple. In the loader and verifier forms, the transition table does not use the choice bit, so the actions for both bits agree. In the scheduler form with no active scheduler state, the same independence holds. The only remaining form is an active scheduler state, which is excluded by the hypothesis. Therefore the two transition actions coincide in all allowed cases.
