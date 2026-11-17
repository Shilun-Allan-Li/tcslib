<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePrefix.lean :: Complexity.PrefixByLength.update_regs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a Single Register

**Claim.** Updating the sole register in the size-$n$ register state to $m$ gives the size-$m$ register state.

**Proof.** To show the two register assignments are equal, compare their values at an arbitrary register. Since there is only one register, that register is the distinguished register $0$. Updating the size-$n$ assignment there replaces its value by $m$, which is exactly the value assigned by the size-$m$ state.
