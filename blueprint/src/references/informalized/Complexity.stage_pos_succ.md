<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stage_pos_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Positive Sets Are Nested

**Claim.** Every string positive at stage $i$ remains positive at stage $i+1$.

**Proof.** The next positive set is formed by the stage update. If the machine accepts, the update preserves the current positive set exactly. If it does not accept, the update inserts the selected witness into that set. In either case, every string already positive at stage $i$ remains positive at stage $i+1}.
