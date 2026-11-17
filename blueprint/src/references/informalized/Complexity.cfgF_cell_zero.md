<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.cfgF_cell_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial work-cell update

**Claim.** If the first input bit is true, the second records whether $z=0$, and the designated chain bit is false, then the local work-cell update rule yields the time-zero encoding of the head indicator, cell content, and work-chain value at $z$.

**Proof.** The true first bit selects the initial-time branch of the local work-cell rule. The false chain bit represents the absent initial predecessor value, as expressed by `optOf_false` (`Complexity.CfgTableau.optOf_false`). The run-at-zero identity (`Turing.MultiTapeTM.runFrom_zero`) reduces the initial configuration to the machine's initialized configuration; its work-tape head starts at position $0$ and its tape is blank. Thus the head-at-$z$ indicator is exactly whether $z=0$, the cell content is absent, and the initial work-chain value is absent. Substituting these initial values into the local rule gives the asserted encoding.

**Key facts.** `Complexity.CfgTableau.optOf_false`, `Turing.MultiTapeTM.runFrom_zero`.
