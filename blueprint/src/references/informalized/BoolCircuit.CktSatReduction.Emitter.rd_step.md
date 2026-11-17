<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachine.lean :: BoolCircuit.CktSatReduction.Emitter.rd_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One read-state transition

**Claim.** From the specified read-state configuration, one machine step is the action prescribed by the transition rule for the read phase, the input symbol at position $i$, and the symbols under the work-tape heads.

**Proof.** A run of one step is the machine’s step applied to the initial configuration. Since the configuration has an active state, the active-state transition rule identifies this step with the action determined by the transition function, evaluated at the input symbol under the head and the symbols under the work-tape heads. The input position defined from $i$ has value $i+1$, so the input-symbol lookup lemma identifies the symbol read there with $w[i]?$; substituting this value gives the stated action.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `BoolCircuit.CktSatReduction.Emitter.step_some`, `Turing.FinTM.inputSymbol_at`.
