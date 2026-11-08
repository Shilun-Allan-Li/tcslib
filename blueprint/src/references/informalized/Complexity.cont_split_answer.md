<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_split_answer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Pair Loader Computes the Verifier

**Claim.** On the word produced by the polynomial split procedure for $y$, the pair-loader machine halts after $3(2|y|+3)$ steps and outputs whether $y$ has a split into an input $x$ and a choice word $u$ of the required polynomial length for which $N$ halts with output $[1]$.

**Proof.** Split according to whether the split solver finds an index. If it finds none, the no-split result (`Complexity.choiceVerifier_no_split`) shows that $y$ is not in the verifier language. The split procedure therefore emits the empty word, and the empty-input computation (`Complexity.cont_pair_empty`) outputs false in one step; monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) extends this to the claimed time. If the solver returns an index $i$, the split specification (`Complexity.certificateSplit_spec`), together with the correspondence between the solver and certificate split (`Complexity.cont_split_bridge`), identifies the split and gives the required length of the suffix. The verifier characterization for concatenated words (`Complexity.choiceVerifier_append`) then says membership is equivalent to $N$ halting on that suffix with output $[1]$. The pair-loader computation result (`Complexity.cont_pair_computes`) computes precisely this indicator on the encoded pair. Finally, the split-word length bound (`Complexity.cont_split_length`) ensures its runtime is at most the target; time monotonicity extends the computation to exactly $3(2|y|+3)$ steps.

**Key facts.** `Complexity.cont_split_bridge`, `Complexity.choiceVerifier_no_split`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.certificateSplit_spec`, `Complexity.choiceVerifier_append`, `Complexity.cont_pair_computes`, `Complexity.cont_split_length`, `Turing.FinTM.ComputesInTime.mono`.
