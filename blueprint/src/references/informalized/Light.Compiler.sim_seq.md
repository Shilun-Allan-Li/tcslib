<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.sim_seq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential Statement Simulation

**Claim.** If the first statement is simulated from $\sigma$ to $\sigma_1$ with cost $c_1$, and the second from $\sigma_1$ to $\sigma_2$ with cost $c_2$, then their sequence is simulated from $\sigma$ to $\sigma_2$ with cost $c_1+c_2$.

**Proof.** Fix a valid starting configuration for the sequence. Its width bound yields width bounds for each component, and its code splits into the first statement followed immediately by the second. The first simulation applies at the original position and state, producing a machine memory related to $\sigma_1$. The operational execution of the first statement preserves boundedness of the state, so this memory and state provide the hypotheses needed to start the second simulation at the position following the first code. Concatenate the two machine runs; the endpoint is the position after the full sequence, and the total step count is the sum of their counts. Adding their individual bounds gives the bound for cost $c_1+c_2$. The second run supplies the final memory relation, while transitivity of agreement outside writable cells combines the two write-set guarantees.

**Key facts.** `Light.Stmt.width_seq_le_iff`, `Light.Compiler.codeAt_seq`, `Light.Compiler.Start.sub`, `Light.Exec.bounded`, `WordRAM.Steps.trans`, `WordRAM.Steps.cast_pos`, `WordRAM.AgreeOutside.trans`.
