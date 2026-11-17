<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfig.lean :: Complexity.eval_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of an Earlier Block

**Claim.** If the list of blocks agrees with the prescribed configuration encoding at every index below $i$, then evaluating a block source referring to any $a<i$ and bit position $j$ gives bit $j$ of the prescribed block at $a$, with false used out of range.

**Proof.** By definition, evaluating the source that refers to block $a$ returns bit $j$ of the list entry at index $a$, using the empty word if that entry is absent. Since $a<i$, the hypothesis identifies that entry with the prescribed configuration block at $a$. Taking its $j$th bit with the same false-padding convention gives the desired equality.
