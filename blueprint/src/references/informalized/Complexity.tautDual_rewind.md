<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding to the Selected State

**Claim.** Starting in rewind state with flag $f$ at position $p\le |x|$ and output $o$, the machine reaches position $1$ after $p+1$ steps, in the anchor state if $f$ is true and in formula-level copying state otherwise. No earlier configuration in this segment is the anchor state.

**Proof.** Induct on $p$. At $p=0$, the head is at the left end. It sees no input symbol, so the rewind transition moves right into the state selected by the flag, without changing the output. This one-step segment has no earlier anchor visit. For the successor case, at position $p+1$ with $p<|x|$, the machine reads bit $x[p]$ and moves left, remaining in the same rewind state and preserving the output. The one-step segment avoids the anchor. The induction hypothesis then rewinds from position $p$ to position $1$ and selects the flagged state. Concatenating the steps yields $(p+1)+1$ steps, as required.

**Key facts.** `Complexity.tautDual_read`, `Complexity.tautDual_action`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.moveInputPos_neg_of_ne_left`, `Complexity.tautDual_segment_one`, `Complexity.tautDual_segment_add`.
