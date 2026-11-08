<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldSafe_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safety After Initialization

**Claim.** Starting the folding simulator on any input over the folded alphabet and taking one step gives a configuration whose state is not the fresh initial state, whose work-head positions are nonnegative, and whose nonnegative work-tape cells have their origin flag set exactly at position zero.

**Proof.** Consider first any action obtained from the initialization action by replacing its successor state with a state $st$ different from the fresh initial state. Applying this action to the initial configuration sets every work-head position to zero. It writes the folded symbol with origin flag true at each head, leaving every other cell blank; consequently, at every nonnegative position $p$, the origin flag is true exactly when $p=0$. The actual start action has one of three forms: the input symbol is absent; it is present but does not decode; or it is present and decodes. In the first and third cases the action is the initialization action, and in the second it has the same initialization data but a halting successor state. Each successor state differs from the fresh initial state, so the preceding verification applies in every case.
