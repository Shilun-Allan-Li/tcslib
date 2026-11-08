<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.prepInvariant_action -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation invariant under an action

**Claim.** Applying a schedule action transforms the preparation invariant into the preparation condition at the action's target phase, moved input position, shifted unary and guide heads, and optionally updated unary tape, while keeping the specified data register, data tapes, and output as arguments unchanged.

**Proof.** Expand the preparation invariant after applying the action: it is the preparation condition evaluated at the resulting state, input-head position, unary and guide head positions, and unary tape. The action sets the state to $q$ and moves the input head by the specified input move, giving the clamped position. Its work-tape instructions shift the unary and guide heads by their respective moves. For the unary tape, split on whether the instruction includes a write: with no write the tape is unchanged; with a write, the scanned cell is updated to the specified symbol. These are exactly the two cases in the definition of $setupWrite$. The budget-tape instruction does not enter the preparation condition, and the data register, data tapes, and output remain the supplied arguments. Thus both sides reduce to the same preparation condition.
