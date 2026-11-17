<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.cfgF_cell_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor work-cell update

**Claim.** Under the stated assumptions on the input bits, decoded snapshot, neighboring head indicators, cell content, and predecessor chain value, the local work-cell update rule produces the encoding of the head indicator, cell content, and work-chain value at time $t+1$ and position $z$.

**Proof.** The false first bit selects the successor-time branch of the local work-cell rule. The hypotheses identify the decoded snapshot and the three neighboring head indicators with their time-$t$ meanings, and identify the encoded content of cell $z$. The two chain bits encode the predecessor chain value; the fact that an optional Boolean is recovered from its presence bit and defaulted value is `optOf_isSome_getD` (`Complexity.CfgTableau.optOf_isSome_getD`). The work-cell transition identity (`Complexity.cell_step`) then gives the head indicator and contents at time $t+1$ from the time-$t$ snapshot and local data. The successor-run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies that next configuration with the machine step from time $t$. Finally, the work-chain recurrence (`Complexity.workChain_eq`) expresses the chain value at $z$ using the updated cell at $z$ and the supplied chain value at $z-1$. These identities yield the claimed encoding component by component.

**Key facts.** `Complexity.CfgTableau.optOf_isSome_getD`, `Complexity.cell_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.workChain_eq`.
