<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformExample.lean :: BoolCircuit.AdjExample.upd_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a Constant Function

**Claim.** For any natural numbers $c,d$, updating the constant function with value $c$ at the unique point of a one-element domain to $d$ gives the constant function with value $d$.

**Proof.** Two functions are equal if they agree at every argument. Any argument in the one-element domain equals its distinguished element, so the update replaces the constant value $c$ by $d$ there. Hence both functions take value $d$ at every argument.
