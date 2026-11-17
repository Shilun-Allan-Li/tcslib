<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Hierarchy.lean :: BoolCircuit.eval_eq_of_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality from List Assignments

**Claim.** If the two circuit families agree on every Boolean list at the list's length, then they agree under every Boolean assignment to every finite set of inputs.

**Proof.** First, the assumed equivalence of the statements that each evaluation equals true implies equality of the two Boolean evaluations on every list. Fix a length $n$ and an assignment $x : 	ext{Fin } n \to \text{Bool}$. Represent $x$ by the list of its values, obtained by enumerating the elements of $\text{Fin } n$. This list has length $n$, and looking up its entry at any index recovers the value of $x$ there. Applying the listwise equality to this list therefore gives equality of the evaluations under $x$.
