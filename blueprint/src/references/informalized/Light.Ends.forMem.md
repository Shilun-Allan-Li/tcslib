<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.forMem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# For-Loop with a Memory Invariant

**Claim.** If the memory invariant holds initially, each loop-body execution preserves the local store and advances the invariant, and the bound expression and cost hypotheses hold, then the for-loop terminates within cost $T$ in a state satisfying $Q$.

**Proof.** Apply the general for-loop theorem (`Light.Ends.for`) with state invariant asserting both that the local store equals the original local store updated at position $i$ to $j$, and that the memory satisfies $I(j)$. The initial update to zero gives this invariant at index zero. In a round, the local-store equality identifies the current state with the input state in the assumed memory-invariant round hypothesis. That execution preserves the local store and establishes $I(j+1)$ in its output memory; a postcondition conversion packages these facts as the state invariant after the loop's increment. The terminal hypothesis gives $Q$, while the bound hypothesis directly supplies safety and value $n$ at each index through $n$. The general theorem's word and cost assumptions are precisely those given, so it concludes the required bounded execution.

**Key facts.** `Light.Ends.for`, `Light.Ends.mono`.
