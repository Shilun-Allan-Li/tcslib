<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run on a Well-Formed Input

**Claim.** If the syntax scan of $x$ from the formula state ends in the exact-end state, then the dual transducer starting in the formula-scanning state at position $1$ with empty output reaches the anchor at position $1$ with the polarity-flipping scan of $x$ as output after exactly $4|x|+4$ steps, with no earlier anchor-state visit.

**Proof.** First scan all of $x$. The suffix-scan lemma (`Complexity.tautDual_scan`) shows that this takes $|x|$ steps, leaves the transducer at the right boundary in the exact-end scanner state, and emits nothing. At that boundary, the scanner’s end-of-input transition moves left into the nonfinal rewind state in one step. The step is justified by reading no input symbol at the right boundary (`Complexity.tautDual_read`), applying the prescribed transition to the configuration (`Complexity.tautDual_action`), and using the one-step head movement to the left (`Turing.moveInputPos_neg_of_ne_left`); it is anchor-free (`Complexity.tautDual_segment_one`). The rewind lemma (`Complexity.tautDual_rewind`) then returns to position $1$ and enters the copy phase, taking $|x|+1$ steps. The copy-scan lemma (`Complexity.tautDual_copy`) scans the input once more, appending the polarity-flipping scan to the output in $|x|$ steps. At the right boundary, the copy-end lemma (`Complexity.tautDual_copy_end`) enters the final rewind state in one step, and the rewind lemma (`Complexity.tautDual_rewind`) returns to position $1$ and reaches the anchor in $|x|+1$ steps. Each of these pieces is an anchor-free segment up to its endpoint, so concatenate them with the segment-composition lemma (`Complexity.tautDual_segment_add`). Their lengths sum to $|x|+1+(|x|+1)+|x|+1+(|x|+1)=4|x|+4$.

**Key facts.** `Complexity.tautDual_scan`, `Complexity.tautDual_read`, `Complexity.tautDual_action`, `Turing.moveInputPos_neg_of_ne_left`, `Complexity.tautDual_segment_one`, `Complexity.tautDual_rewind`, `Complexity.tautDual_copy`, `Complexity.tautDual_copy_end`, `Complexity.tautDual_segment_add`.
