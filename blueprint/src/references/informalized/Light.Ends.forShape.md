<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.forShape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Execution of a Shaped Loop

**Claim.** If the shaped state family satisfies the initial, round, terminal, bound, counter, and successor conditions, then the for-loop from the specified initial state terminates within cost $T$ in a state satisfying $Q$.

**Proof.** Use the general for-loop theorem (`Light.Ends.for`) with invariant saying that the current state is some $S(j,s,\mu')$ and that $I(j,\mu')$ holds. The initial equality identifies the state after setting the counter to zero with $S(0,s_0,\mu)$, so the base invariant follows. For each $j<n$, the shaped round hypothesis gives an execution to another state in the family with invariant at $j+1$. The counter property identifies the current index, and the successor property identifies the state after the loop's increment with the corresponding next shaped state; thus the round postcondition has the form required by the general theorem. At index $n$, the terminal hypothesis gives $Q$. The bound hypothesis supplies safety and value $n$ for the loop condition, and the word and cost bounds are unchanged. These facts establish all hypotheses of the general theorem and yield the conclusion.

**Key facts.** `Light.Ends.for`, `Light.Ends.mono`.
