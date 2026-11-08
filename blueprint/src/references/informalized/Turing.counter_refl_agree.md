<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_refl_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement for the Identity Embedding

**Claim.** The counter-loop machine using the identity embedding of Boolean symbols agrees with the Boolean counter-loop machine at every state and every transition input.

**Proof.** It is enough to compare transitions in each of the four counter-loop state constructors. In a body state, both machines use the same embedded body machine and redirect its successor state in the same way; their actions therefore agree by definition. In the done and escape states, both machines perform the same stationary transition. In a decrement state, first note that lifting a Boolean machine through the identity embedding leaves its transition unchanged: decoding each optional Boolean symbol returns that symbol, and relabelling written symbols by the identity does likewise. Embedding a one-tape machine into the last tape of the larger machine reads the symbol at that last tape and performs precisely its action there, leaving the other work tapes untouched. Applying these observations to the decrement machine shows that the two decrement transitions have the same input movement, work-tape actions, output, and successor phase after the same state redirection. Hence the transitions agree for all states and inputs.
