<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: Language.mem_parity_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity and Boolean XOR

**Claim.** A Boolean word has an odd number of true entries exactly when folding Boolean XOR over the word, starting from `false`, gives `true`.

**Proof.** Proceed by induction on the word. The empty word has zero true entries, and its XOR fold is `false`, so both sides are false. For a word formed by adjoining a bit $b$ to a word $w$, if $b$ is false, the true-entry count and XOR fold are unchanged, and the induction hypothesis applies. If $b$ is true, the count increases by one, so its parity flips. The XOR fold is likewise the negation of the fold for $w$: when that fold is false the new count is odd and the new fold is true; when it is true the new count is even and the new fold is false. Thus the two conditions agree in either case.
