<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.roundTM_visited -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Positions During a Round

**Claim.** Under the stated representation and entry-phase hypotheses, there is a bounded run of the simulating machine that reaches the exit corresponding to the selected action, represents the post-action configuration, avoids the entry and halt anchors at intermediate times, preserves the output, and obeys the stated bounds on visited tape-head positions.

**Proof.** Apply `roundTM_effect` to obtain a run length $T$ and the endpoint, representation, output, intermediate-state, and head-environment bounds. For an original tape head, any position in its visited set is its position at some time $u\le T$. The head-environment bound says this position is either its initial position or its endpoint position; the representation relations identify these with the head positions in $c$ and in the post-action configuration. Thus every visited position belongs to the claimed two-element set. For either auxiliary tape, the corresponding environment bound controls the absolute displacement from its initial head position. The representation hypothesis places that initial position at $0$, so the displacement bound gives membership in the claimed symmetric interval. The time bound and remaining conclusions are inherited directly from `roundTM_effect`.

**Key facts.** `Turing.StepBlock.roundTM_effect`.
