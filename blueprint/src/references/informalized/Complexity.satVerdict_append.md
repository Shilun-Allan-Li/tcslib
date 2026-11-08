<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satVerdict_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verdict on a concatenated encoding

**Claim.** When $|u|=|x|+1$, the verifier verdict on $x$ concatenated with $u$ equals the conjunction of the mode-guarded width-three test of the formula decoded from $x$ and the evaluation of that formula under the assignment carried by $u$.

**Proof.** The verifier searches for a split point $i$ satisfying the encoding equation $i+(i+1)=|x|+|u|$. Since $|u|=|x|+1$, the total length is $|x|+(|x|+1)$, so the split is exactly at $|x|$ by the split-existence result (`Complexity.sat_split_exists`). Consequently the verifier decodes the prefix $x$ and uses the suffix $u$ as the assignment word. Unfolding these definitions gives the stated conjunction; the remaining simplification is the direct behavior of list concatenation, prefix, and suffix.

**Key facts.** `Complexity.sat_split_exists`.
