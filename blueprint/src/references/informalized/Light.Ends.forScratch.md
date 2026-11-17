<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.forScratch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# For-Loop with Refreshed Scratch Locals

**Claim.** Under the stated memory-invariant, round, terminal, bound, local-assignment, counter-exclusion, word-limit, and cost hypotheses, the for-loop from the initial framed state terminates within cost $T$ in a state satisfying $Q$.

**Proof.** Apply the general for-loop theorem (`Light.Ends.for`) with invariant asserting that the loop's locals agree with the initial list frame outside the counter and scratch indices, and that the memory satisfies $I(j)$. The initial update to zero preserves the required local agreement because the counter index is outside the scratch list, and the assumed initial memory invariant supplies the rest. For a round, the local-agreement condition identifies the current state with the supplied state whose locals are refreshed along the scratch indices and whose counter is $j$. The round hypothesis executes the body and advances the memory invariant. The preservation-of-untouched-locals result (`Light.Ends.keeping`), applied to that execution, shows that every local outside the body's assigned indices remains unchanged. Since every assigned index lies in the scratch list, and the counter is outside that list, the counter remains $j$ and the other required local agreements persist; after incrementing, the loop invariant holds at $j+1$. At termination, the same state-shape identification lets the terminal hypothesis provide $Q$. The bound hypothesis gives safety and value $n$ in each invariant state, and the stated word and cost bounds complete the application of the general loop theorem. The local-state identifications used here follow from the frame formulas for setting one position (`Light.frame_setLocal`) and refreshing a list of positions (`Light.frame_refreshLocals`).

**Key facts.** `Light.Ends.for`, `Light.Ends.keeping`, `Light.Ends.mono`, `Light.frame_setLocal`, `Light.frame_refreshLocals`.
