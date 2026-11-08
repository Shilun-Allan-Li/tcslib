<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.outSummary_append_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Append invariance of output summaries

**Claim.** If two finite Boolean strings have the same output summary, then appending the same finite Boolean string to both preserves equality of their output summaries.

**Proof.** Fix the appended string $e$. For any string $a$, its summary after appending $e$ is determined solely by the summary of $a$: an empty summary becomes the summary of $e$; an accepting summary remains accepting when $e$ is empty and otherwise becomes dead; a dead summary remains dead. This follows by splitting on whether $a$ is empty, the one-bit string $[1]$, or any other string, and evaluating the definition of the summary. Applying this description to both $u$ and $v$, their equal initial summaries give equal summaries after appending $e$.
