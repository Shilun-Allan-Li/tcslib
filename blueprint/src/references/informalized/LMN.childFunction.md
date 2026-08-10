<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: childFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The function computed by a subcircuit over gate functions

**Definition.** For a subcircuit `c_sub : Circuit m` and gate functions
`gates : Fin m → (Fin n → Bool) → Bool`,

`childFunction c_sub gates = fun x => c_sub.eval (fun i => gates i x)`.

That is: `c_sub` is read as a circuit whose `m` inputs are the gates, and feeding
it the gate values at `x` gives a Boolean function of the original `n` variables.
Purely a naming device for the composition `c_sub.eval ∘ (gates · x)` — no
properties are proved about it.

**Status.** Dead declaration: nothing in the repository references
`childFunction`. The lemmas that would use it (`or_of_lit_children_dnf`,
`child_depth_le1_has_signed_dnf`, `exists_circuit_depth_reduction`) all spell the
composition `fun x => c.eval (fun i => gates i x)` out by hand instead.
