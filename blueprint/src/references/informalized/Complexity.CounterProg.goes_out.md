<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_out -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Printing a Bit

**Claim.** If the instruction at $\ell$ prints $b$ and continues at $\ell'$, then from any output $o$ the program reaches $\ell'$ in at most one step, preserving registers and input position and appending $b$.

**Proof.** For any initial output $o$, the specified instruction performs one transition to $\ell'$. It leaves the registers and input position unchanged and appends the single bit $b$ to the output. The one-step transition principle (`Complexity.CounterProg.goes_of_step`) therefore yields the claimed run bound.

**Key facts.** `Complexity.CounterProg.goes_of_step`.
