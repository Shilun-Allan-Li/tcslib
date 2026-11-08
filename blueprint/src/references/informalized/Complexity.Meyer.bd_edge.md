<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSoundInput.lean :: Complexity.Meyer.bd_edge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Boundary Consistency

**Claim.** Under the local checker and correctness hypotheses, a halting state or stationary input-head move satisfies the boundary claim automatically; for a right or left move, either the current read is blank and the table predicts no symbol there, or the table predicts no symbol at the corresponding boundary after the next step.

**Proof.** Apply the local checker hypothesis to the boundary-check instance at time $t$, address $0$, and input index $|x|+1$. Correctness identifies the state and reads represented in that instance with those of the actual configuration, so the checker condition reduces to the boundary predicate for that configuration. The correspondence between the encoded symbol test and the signed input read is supplied by $\texttt{symvA\_NumVal}$, and the two sign choices are converted to actual reads by $\texttt{sv\_sgn}$.

If the configuration is halting, the claim is immediate. Otherwise split on the transition’s input-head move. A stationary move makes the claim automatic. For a right move, the reduced checker condition gives the disjunction between a blank current read together with a blank prediction at the moved-to position, and a blank prediction at the right boundary at time $t+1$. Rewriting the symbol tests as input reads yields exactly the stated alternative. For a left move the same reduction gives the corresponding alternative at the left boundary. Thus the required boundary claim follows in each movement case.

**Key facts.** `Complexity.Meyer.claims_of_correct`, `Complexity.Meyer.symvA_NumVal`, `Complexity.Meyer.sv_sgn`.
