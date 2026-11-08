<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePrefix.lean :: Complexity.PrefixByLength.goes_dec_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decrementing the Register Once

**Claim.** For either program parameter, every input and all $n,p$, starting at the decrement label with register $n+1$ and position $p$, the program reaches the head label in one step with register $n$, unchanged position, and no new output. This holds for any output already printed.

**Proof.** At the decrement label, the instruction decrements the single register and moves to the head label in one step (`Complexity.CounterProg.goes_dec`). Since the register initially contains $n+1$, its decremented value is $(n+1)-1=n$. The register assignment obtained by updating its sole coordinate to this value is exactly the assignment with value $n$ (`Complexity.PrefixByLength.update_regs`).

**Key facts.** `Complexity.CounterProg.goes_dec`, `Complexity.PrefixByLength.update_regs`.
