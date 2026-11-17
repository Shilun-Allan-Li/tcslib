<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Assigns.lean :: Light.Ends.keeping -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Unassigned Locals

**Claim.** A bounded execution can be chosen to end in a state satisfying $Q$ in which every local not assigned by the statement retains its initial value.

**Proof.** Unpack the bounded-execution hypothesis to obtain a final state, an execution cost, the execution itself, its cost bound, and the fact that $Q$ holds in the final state. Keep that same execution, cost, and final state. The execution preserves every local whose index is absent from the statement's assignment list (`Light.Exec.loc_eq_of_notMem_assigns`), so the final state also satisfies the required equalities for all unassigned locals.

**Key facts.** `Light.Exec.loc_eq_of_notMem_assigns`.
