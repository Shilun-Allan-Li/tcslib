<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.FinTM.liftSymbols_computesFunInTimeVia -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computation Under Alphabet Embedding

**Claim.** If a finite Boolean Turing machine computes $f$ in time $T$, then lifting its symbols along an embedding $e$ into an alphabet $\Gamma$ computes the letterwise $e$-image of $f(x)$ on the encoded input $x.map(e)$ within the same time bound.

**Proof.** Fix an input $x$. The computation hypothesis, expressed as halting with output $f(x)$ at time $T(|x|)$, follows from the characterization of time-bounded computation (`computesInTime_iff`). The lifted machine’s initial configuration on $x.map(e)$ is the symbol-lift of the original initial configuration (`liftSymbols_initCfg`), and its run for the same number of steps is the symbol-lift of the original run (`liftSymbols_runFrom`). Lifting preserves the state, so the lifted run is halted; its output is the letterwise image under $e$ of the original output, namely $(f(x)).map(e)$. The computation characterization converts these two facts back into the required time-bounded computation.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.liftSymbols_initCfg`, `Turing.MultiTapeTM.liftSymbols_runFrom`.
