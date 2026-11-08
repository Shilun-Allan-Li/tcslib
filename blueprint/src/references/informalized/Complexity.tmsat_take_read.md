<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_take_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol at a configuration position

**Claim.** In the specified configuration on input $x$, whose input head is at position $i$, the symbol under the head is the bit $x_i$ when $i<|x|$, and is blank when $i=|x|$.

**Proof.** The configuration stores its input-head position with an offset of one: the stored position has value $i+1$. The general input-position lemma (`Turing.FinTM.inputSymbol_at`) says that a configuration with stored position $i+1$ reads exactly the list entry at index $i$, using the usual option-valued indexing that returns blank at the end of the list. The given bound $i\le |x|$ ensures this covers both an actual input bit and the blank immediately after the input.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
