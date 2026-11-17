<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.stage_new -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# New Positive Strings at a Stage

**Claim.** If a Boolean string is positive at stage $i+1$ but not at stage $i$, it is the witness selected at stage $i$, and machine $N_i$ does not accept its specified unary input within the stage time bound relative to the stage-$i$ positive-set oracle.

**Proof.** The positive set at stage $i+1$ is obtained by the stage update. If the machine accepts, that update leaves the positive set unchanged, contradicting that $z$ was absent at stage $i$. Thus the machine does not accept. In the nonaccepting case, the update inserts exactly the selected witness into the previous positive set. Since $z$ is in the updated set but was not in the previous one, it must be that witness.
