<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.foldl_vStepO_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of cell updates

**Claim.** Folding the option-valued update over the list formed by making every cell in $L$ present gives the same state as folding the ordinary cell update over $L$.

**Proof.** Induct on $L$, allowing the initial state to vary. For the empty list both folds leave the state unchanged. If $L$ begins with a cell $cv$, its option-valued version begins with `some cv`; by definition, this update is exactly the ordinary update on $cv$. The induction hypothesis identifies the remaining folds from the resulting state, and hence the two final states agree.
