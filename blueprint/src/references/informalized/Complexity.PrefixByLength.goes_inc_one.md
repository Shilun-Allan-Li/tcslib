<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePrefix.lean :: Complexity.PrefixByLength.goes_inc_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Incrementing the Register Once

**Claim.** For either program parameter, every input and all $n,p$, starting at the bump label with register $n$ and position $p$, the program reaches scan in one step with register $n+1$, unchanged position, and no new output. This holds for any output already printed.

**Proof.** The bump instruction increments the sole register and moves to scan in one step (`Complexity.CounterProg.goes_inc`). Updating the register assignment at its only coordinate to $n+1$ gives precisely the assignment with value $n+1$ (`Complexity.PrefixByLength.update_regs`).

**Key facts.** `Complexity.CounterProg.goes_inc`, `Complexity.PrefixByLength.update_regs`.
