<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.entry_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Newly Added Word

**Claim.** If a word enters the positive set at stage $s+1$ but was absent at stage $s$, its length equals the fresh length chosen using the bound stored at stage $s$.

**Proof.** The stage-transition characterization (`Complexity.stage_new`) says that any word newly in the positive set must equal the witness selected at stage $s$, when the stage data is that of stage $s$. The witness-length property (`Complexity.stageWit_spec`) states that this selected word has length exactly the fresh length determined by $s$ and that stage's bound. Substituting the witness for the newly added word gives the result.

**Key facts.** `Complexity.stage_new`, `Complexity.stageWit_spec`.
