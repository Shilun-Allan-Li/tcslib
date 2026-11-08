<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satHost_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Module at a Host Call Site

**Claim.** If module $i$ satisfies the clean-module contract, then for every input, argument, and output prefix, the host reaches its return state with the contract's result and emitted word within the module's time bound, without visiting the loop-anchor state earlier.

**Proof.** Apply the clean-module contract to $x$ and $\mathrm{arg}$. It supplies a time $t$ with $0<t\le B(|\mathrm{arg}|)$, no halting at any earlier time, and a halted configuration whose tape contents encode $f(\mathrm{arg})$ and whose output is $g(\mathrm{arg})$. The positive work-tape hypothesis lets the host call result apply. That result transfers the module run to the host: before $t$ the host avoids the loop-anchor state, and at $t$ it is in the module's return state with the required tapes and output prefix concatenated with $g(\mathrm{arg})$ (`Complexity.satHost_call`). Keeping the same time $t$ proves the claim.

**Key facts.** `Complexity.satHost_call`.
