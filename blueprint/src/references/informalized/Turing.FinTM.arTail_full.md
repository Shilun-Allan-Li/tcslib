<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arTail_full -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the write sweep

**Claim.** At counter $N+1$, the write-sweep block family agrees at every position with the original tape coded blockwise.

**Proof.** Fix a block position $z$ and an offset $j\in\{0,\ldots,N\}$. Since $j\le N$, the condition $N+1\le j$ is false. Thus the clause that substitutes the newly written symbol does not apply, and the block entry is $E(t(z))_j$. This holds for every $z$ and $j$, so the two block families are equal.
