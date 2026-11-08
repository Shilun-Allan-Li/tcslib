<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogMarker_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dichotomy for the Last-True Split

**Claim.** A Boolean word either has no true bit and its last-true split is undefined, or its last-true split is a word $u$ such that every prefix $p$ satisfies that the split of $pv$ is $pu$.

**Proof.** Induct on the word by removing its final bit. For the empty word, there is no true bit and the split is undefined. Suppose first that the final bit is false. Appending this bit changes neither whether the word contains a true bit nor the suffix after its last true bit. Thus either the no-true-bit case persists, or the induction hypothesis supplies a suffix $u$ and its prefix property continues to hold for the extended word. If instead the final bit is true, it is the last true bit, so the split is the word consisting of the preceding part, and the word contains a true bit. For any prefix $p$, the last true bit of the concatenation is still this final bit, so its split is the concatenation of $p$ with that preceding part.
