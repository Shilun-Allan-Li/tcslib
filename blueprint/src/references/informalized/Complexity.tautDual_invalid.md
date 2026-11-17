<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_invalid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return After an Invalid Scan

**Claim.** If scanning $x$ from the formula-level state does not end in the exact-end state, then starting the transducer in formula-level scanning state at position $1$ with empty output reaches the anchor at position $1$ with output $[0]$ after $2|x|+2$ steps, with no earlier anchor visit.

**Proof.** First, the scan lemma processes all of $x$: after $|x|$ steps the machine is in scanning state carrying the final syntax state, at position $|x|+1$, with empty output. Because that syntax state is not the exact-end state, the end-of-input transition moves left into rewind state with flag true and emits the single bit $0$. The one-step segment lemma applies, and the move places the head at position $|x|$; this transition does not visit the anchor. Finally, the rewind lemma with true flag returns the head from position $|x|$ to position $1$ in $|x|+1$ steps, reaching the anchor without visiting it earlier in that segment. Concatenating these three segments gives $|x|+1+(|x|+1)=2|x|+2$ steps and the stated output and endpoint.

**Key facts.** `Complexity.tautDual_scan`, `Complexity.tautDual_read`, `Complexity.tautDual_action`, `Turing.moveInputPos_neg_of_ne_left`, `Complexity.tautDual_segment_one`, `Complexity.tautDual_rewind`, `Complexity.tautDual_segment_add`.
