<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardVerifier.lean :: Complexity.TQBFHard.pt_blkAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Block Slice

**Claim.** If the offset can be supplied as a unary word in polynomial time, then the indicated slice of the extracted second component, with length $A(|x|+1)^a$, is polynomial-time computable.

**Proof.** The second component extracted from $y$ is polynomial-time computable (`polyTimeComputable_pairSndD`). Given the assumed unary output for the offset, the variable-drop construction computes that component after dropping the first $o(y)$ bits (`pt_drop`). Independently, the width $A(|x|+1)^a$ can be supplied in unary in polynomial time (`pt_vwid`). The variable-take construction therefore truncates the dropped word to exactly that width in polynomial time (`pt_take`). This is the required slice.

**Key facts.** `Complexity.TQBFHard.pt_drop`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.TQBFHard.pt_vwid`, `Complexity.TQBFHard.pt_take`.
