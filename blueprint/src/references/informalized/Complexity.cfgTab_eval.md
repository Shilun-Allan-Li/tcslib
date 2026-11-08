<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.cfgTab_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Tableau Evaluation

**Claim.** The configuration tableau circuit evaluates to true exactly when some transition before time $T$ emits true during the machine’s run on $z$ followed by the input bits.

**Proof.** First, the layout of the initial input word is valid (`Complexity.tabLayout_valid`), so the configuration program is well formed and has the required fixed source-list lengths (`Complexity.cfgProg_wf`). The requested snapshot index lies within the program: the program length is given by `Complexity.length_cfgProg`, the layout length by `Complexity.length_tabLayout`, and `Complexity.snapIdx_lt_succ` bounds the snapshot index. The input word $z$ followed by the bits of the assignment has length $|z|+n$.

Apply the tableau circuit evaluation theorem (`BoolCircuit.tabCircuit_eval`) at that snapshot index and the designated output bit. It identifies the circuit output with that bit of the computed program block. The program-block description (`Complexity.cfgProg_blocks`) identifies the block with the configuration expansion at the same index. The snapshot-index expansion theorem (`Complexity.cfgExp_snapIdx`) then identifies that expansion with the snapshot at time $T$; the layout evaluates to the original input word by `Complexity.tabLayout_eval`.

Finally, substituting the snapshot expansion and the input word into the output expression reduces it to the tableau’s acceptance condition. By the definition of that condition (`tableauAccepted`), its Boolean value is true exactly when some time $s<T$ has emitted `true`, as claimed.

**Key facts.** `Complexity.tabLayout_valid`, `Complexity.cfgProg_wf`, `Complexity.length_cfgProg`, `Complexity.length_tabLayout`, `Complexity.snapIdx_lt_succ`, `BoolCircuit.tabCircuit_eval`, `Complexity.cfgProg_blocks`, `Complexity.cfgExp_snapIdx`, `Complexity.tabLayout_eval`.
