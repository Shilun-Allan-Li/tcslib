<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stage_pos_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Positive Sets

**Claim.** Whenever $i\le j$, every string positive at stage $i$ is positive at stage $j$.

**Proof.** Induct on the stage index $j$, using induction along the relation $i\le j$. When $i=j$, inclusion is immediate. For the successor step, the induction hypothesis includes the stage-$i$ positive set in the current stage-$j$ positive set; the successive-stage nesting property includes that set in the stage-$(j+1)$ positive set. Composing these inclusions proves the result.

**Key facts.** `Complexity.stage_pos_succ`.
