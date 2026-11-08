<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.MultiTapeTM.liftSymbols_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting a Computation

**Claim.** For a Boolean-symbol machine $M$, an embedding $e$ into a symbol type with decidable equality, a Boolean input $x$, a configuration $c$ on $x$, and any $t\in\mathbb{N}$, running the lifted machine from the lifted configuration for $t$ steps gives the lift of the configuration reached by running $M$ from $c$ for $t$ steps.

**Proof.** Induct on the number of steps, with the starting configuration allowed to vary. At zero steps both sides are the lifted starting configuration. For the successor case, express each run as one step followed by the remaining run, using the successor-step identity (`Turing.MultiTapeTM.runFrom_succ_eq_step`). The one-step compatibility of lifting (`Turing.MultiTapeTM.liftSymbols_step`) identifies the lifted machine's first step with the lift of the original machine's first step. Apply the induction hypothesis to that resulting configuration to identify the rest of the runs. This proves the equality at every step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.liftSymbols_step`.
