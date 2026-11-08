<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Wrappers.lean :: Turing.emit_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forwarding Commutes with Applying an Action

**Claim.** Applying the forwarded action to the forwarded configuration with output prefix $p$ gives the forwarded image of the result of applying the original action.

**Proof.** The forwarded action retains the input and work-tape operations, so applying it to the forwarded configuration produces the same input-head position, work-tape contents, and work-head positions as applying the original action before forwarding. Its successor state is the forwarded version of the original action's successor, with the chosen return state used when the action halts; this is exactly the state assigned by forwarding the resulting configuration. For the output, the left side appends the action's output to the prefixed output, giving $(p\mathbin{++}c.output)\mathbin{++}a.output.toList$. The right side gives $p\mathbin{++}(c.output\mathbin{++}a.output.toList)$. These agree by associativity of list concatenation, so all configuration components match.
