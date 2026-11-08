<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Logic.lean :: Light.Ends.set -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded assignment execution

**Claim.** If an expression is safe in the initial state, its cost plus one is at most the time bound, and the postcondition holds after updating local $x$ to the expression's value, then assigning the expression to $x$ ends within the bound and satisfies the postcondition.

**Proof.** Use the assignment execution rule to exhibit the updated state as the result of execution, with cost exactly the expression's cost plus one. The assumed cost bound and postcondition then give the required bound and final-state property.
