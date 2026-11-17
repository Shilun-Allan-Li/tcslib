<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgInput_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input symbol under aligned heads

**Claim.** When the input-head positions of $c$ and $d$ correspond under transfer to the longer word, retracting the symbol read by $d$ gives the symbol read by $c$.

**Proof.** The position transfer preserves the numerical value of the head position, and the retracted word has the same length as the original word. Thus the two input-symbol definitions test the same boundary positions: the left end and the position just beyond the word. If either boundary test applies, both reads are blank, so their retractions agree. Otherwise both definitions select the list entry at the same index. Retracting an entry of the pointwise-mapped word gives the corresponding entry of the retracted word, proving the equality.
