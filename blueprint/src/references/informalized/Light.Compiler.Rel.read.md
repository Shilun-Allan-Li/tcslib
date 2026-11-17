<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.Rel.read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a bounded memory address

**Claim.** At any integer address within the space limit, the memory stores the encoding of the light state's memory value at the corresponding natural-number address.

**Proof.** The address bounds imply that its natural-number conversion is below the space limit. The memory clause of the relation, applied at that natural address, gives the encoding of the light memory value there. Since the address is nonnegative, converting it to a natural number and then back to an integer returns the original address, yielding the stated equality.
