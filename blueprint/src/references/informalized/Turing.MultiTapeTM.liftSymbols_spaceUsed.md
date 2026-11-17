<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.MultiTapeTM.liftSymbols_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Space Under Symbol Lifting

**Claim.** For a Boolean-symbol machine $M$, an embedding $e$ into a symbol type with decidable equality, a Boolean input $x$, a configuration $c$ on $x$, and any $t\in\mathbb{N}$, the total number of work-tape cells visited through step $t$ by the lifted computation equals that for the original computation.

**Proof.** For each work tape, the visited cells through step $t$ are the set of head positions appearing at times from $0$ through $t$. The computation-lifting theorem (`Turing.MultiTapeTM.liftSymbols_runFrom`) identifies the lifted configuration at every such time with the lift of the original configuration. Lifting a configuration preserves each work-head position, so these two finite sets of visited positions coincide tape by tape. Their cardinalities therefore agree; summing those cardinalities over all work tapes gives equality of the total space used.

**Key facts.** `Turing.MultiTapeTM.liftSymbols_runFrom`.
