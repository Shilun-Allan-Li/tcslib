<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Main.lean :: Complexity.LogProg.ExpBFS.acc_orcN -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Oracle Characterization

**Claim.** For a finite-state nondeterministic Turing machine $N$, the oracle at index $3$ answers true on the encoding of $x$ paired with the binary encodings of $u$ and $r$ exactly when that string belongs to $N$’s acceptance language.

**Proof.** By definition, the oracle at index $3$ is the indicator function of the language selected by the fourth entry of the decider list, which is the acceptance language. An indicator takes the value true exactly on members of its set (\texttt{indicator_eq_decide}); unfolding these definitions gives the stated equivalence.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`.
