<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean :: BoolCircuit.CircuitEval.leadOnes_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading ones in a padded word

**Claim.** A word of $n$ ones followed by zero and then any Boolean word has exactly $n$ leading ones.

**Proof.** Induct on $n$. For $n=0$, the word begins with zero, so its initial run of ones has length zero. For the successor case, the word begins with one followed by a word with $n$ ones, then zero, then the remaining word. Removing that first one leaves the induction-hypothesis word, whose leading-one count is $n$; reinstating the first one gives $n+1$.
