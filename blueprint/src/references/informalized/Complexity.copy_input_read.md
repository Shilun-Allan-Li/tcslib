<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.copy_input_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbol Read at the Copy Position

**Claim.** If $j\le |x|$ and the input head is at position $j+1$, then the symbol read is the embedded bit at position $j$ when $j<|x|$, and is blank when $j=|x|$.

**Proof.** Split according to whether $j<|x|$. In that case, the input head is at the position corresponding to the $j$th input symbol, and the interior-read formula (Turing.inputSymbolInner) identifies the read with that symbol. The input word is formed by embedding each bit of $x$, so the read is the embedded bit at $j$. Otherwise, $j\le |x|$ gives $j=|x|$. The head is then at the right blank boundary of the input, so the blank-boundary characterization (Complexity.inputSymbol_blank) says the read is blank. In this endpoint case the optional lookup $x[j]? $ is also absent, giving the stated formula in both cases.

**Key facts.** `Turing.inputSymbolInner`, `Complexity.inputSymbol_blank`.
