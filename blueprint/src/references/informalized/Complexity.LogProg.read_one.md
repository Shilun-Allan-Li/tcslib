<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.read_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One step of the read model

**Claim.** From the prescribed configuration in phase $\mathrm{ph}$, one step of the read model is exactly the configuration obtained by applying the read transition to the scanned input symbol and scanned work-tape symbols.

**Proof.** A one-step run is the single transition of the register program (`rrun_one`), and because the state is a read phase where the model has no call, that transition is the underlying machine step (`rstep_noncall`). The configuration's input-symbol accessor agrees with the list lookup at the shifted input-head position, with the left boundary interpreted as blank (`inputSymbol_eq`). Unfolding the read model then identifies its machine transition with the prescribed read transition; the definitions of the setup configuration give the stated scanned work symbols.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.rstep_noncall`, `Complexity.LogProg.inputSymbol_eq`.
