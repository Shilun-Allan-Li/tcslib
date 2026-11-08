<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Host_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Host Call

**Claim.** Under the clean-contract hypothesis for module $i$, the host started at that module’s entry with argument $\mathrm{arg}$ avoids the loop anchor at every time before the contract’s halting time $t$, and at time $t$ reaches the resolved return with tape word $f(\mathrm{arg})$ and output $\mathrm{pre} ++ g(\mathrm{arg})$. The same positive time bound from the contract applies.

**Proof.** Apply the clean-contract assumption to $x$ and $\mathrm{arg}$. It supplies a positive time $t\le B(|\mathrm{arg}|)$, no earlier halting, and the module’s halting configuration with tape word $f(\mathrm{arg})$ and output $g(\mathrm{arg})$. The positive tape-count clause of the contract lets us apply the host-call simulation result (`clA5Host_call`) to this run. That result transfers the module’s run to the host: before time $t$ the host state is never the loop anchor, and at time $t$ its configuration has the resolved return state, the specified tape word, and output prefix followed by the module’s output. Retaining the time and its bounds from the contract gives the conclusion.

**Key facts.** `Complexity.clA5Host_call`.
