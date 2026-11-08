<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clQuery_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration of the Query Machine

**Claim.** On the packed query words, the query machine’s initial configuration has its initial control state, blank candidate and flag tapes, the stream and target words in their designated locations, a unary clock of length $N$ with head at zero, blank remaining cells, and empty output.

**Proof.** Both configurations have the same initial control state, input-head position, and empty output. For each work-tape coordinate, split into the row-coordinate block and the five auxiliary coordinates. In the row block, the configuration built from words has blank tapes, agreeing with the empty candidate fields. In the auxiliary block, the five query words place the stream, the two targets, and the unary clock in their designated tapes; the remaining flag tape is blank. Their head positions are respectively zero for the stream, targets, and clock, and zero for the blank flag tape. Thus every work tape and head position agrees, so the configurations are equal.
