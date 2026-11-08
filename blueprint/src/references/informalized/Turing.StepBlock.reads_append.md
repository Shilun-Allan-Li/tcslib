<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.reads_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reads on Concatenated Words

**Claim.** If the cells along the concatenation of $a$ and $b$ agree with that word, then the cells along $a$ and the subsequent cells along $b$ agree with their respective words.

**Proof.** For any position $r<|a|$, the hypothesis applies at offset $r$ in the concatenation. At that index, the concatenated word has the same entry as $a$, giving the first assertion. For any $r<|b|$, apply the hypothesis at offset $|a|+r$. The concatenated word’s entry there is the $r$-th entry of $b$, since the second list begins immediately after the first. This gives the second assertion, with the cell position written as $p+|a|+r$.
