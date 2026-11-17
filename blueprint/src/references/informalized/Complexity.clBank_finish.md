<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBank_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simultaneous Selected Counter Increments

**Claim.** After $2W+2$ steps, each counter is in return control with its head at cell zero; counter $i$ holds the binary representation of $n(i)+1$ if selected and of $n(i)$ otherwise, while the input position remains $p$ and the output remains empty.

**Proof.** The bank run is coordinatewise: after any fixed number of steps, each component is the corresponding single-counter machine run for that same number of steps (`Complexity.clBank_run`). Apply the one-counter result to each coordinate, using the given width bound for that counter; it identifies the component at time $2W+2$ as the required return-control configuration (`Complexity.clBank_component`). Since this holds for every coordinate, the bank configuration is exactly the one asserted.

**Key facts.** `Complexity.clBank_run`, `Complexity.clBank_component`.
