<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Correct.lean :: Complexity.LogProg.TQBFARM.call_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Bounded Calls

**Claim.** Under the stated input encoding and bounds, for every $j,k$ with $k+j=|qs|$, the machine call from depth $k$ has the specified return behavior and respects the validity and register bounds.

**Proof.** Induct on $j$. When $j=0$, the equation $k+j=|qs|$ forces $k=|qs|$. The leaf case is exactly the conclusion supplied by the leaf correctness theorem (`leaf_spec`). For the successor step, write the number of remaining quantifiers as $j+1$. The equation $k+(j+1)=|qs|$ implies $k<|qs|$, and also $(k+1)+j=|qs|$. Apply the induction hypothesis at depth $k+1$ to obtain correctness of the call there. The inner correctness theorem (`inner_spec`), using this child-call result and the same input and bound assumptions, then establishes the required call behavior at depth $k$.

**Key facts.** `Complexity.LogProg.TQBFARM.leaf_spec`, `Complexity.LogProg.TQBFARM.inner_spec`.
