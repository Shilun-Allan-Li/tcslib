<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.cfgCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the configuration circuit

**Claim.** For a valid list of bit sources and an input $x$, the configuration circuit evaluates to true exactly when some time $s<T$ in the run on the source-evaluated word emits the bit $1$.

**Proof.** First, the snapshot vertex at time $T$ lies within the compiled program: its index is below the next time block, and the program length is $(T+1)$ times the configuration stride (`Complexity.length_cfgProg`, `Complexity.snapIdx_lt_succ`). The well-formedness and source-width properties of the generated program (`Complexity.cfgProg_wf`) allow the general evaluation theorem for program circuits (`BoolCircuit.progCircuit_eval`) to identify the circuit's output with the corresponding output bit of the computed block. The block-correctness theorem (`Complexity.cfgProg_blocks`) identifies that block with the configuration expansion on the word obtained by evaluating each source on $x$. At the snapshot index, the expansion is the snapshot encoding (`Complexity.cfgExp_snapIdx`); unpacking its acceptance bit yields precisely the condition that an emission of $1$ occurs at some time strictly below $T$.

**Key facts.** `Complexity.length_cfgProg`, `Complexity.snapIdx_lt_succ`, `Complexity.cfgProg_wf`, `BoolCircuit.progCircuit_eval`, `Complexity.cfgProg_blocks`, `Complexity.cfgExp_snapIdx`.
