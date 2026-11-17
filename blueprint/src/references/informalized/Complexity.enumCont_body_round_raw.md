<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_round_raw -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Raw body round

**Claim.** Starting just after departure in mode 1, the body machine reaches the accepting halted configuration when the verification output bit is true, and otherwise returns to the anchor carrying the incremented word, with overflow represented by the original word, within the stated time bound.

**Proof.** Run the body-call simulation on the verification computation from state $q_v$, in mode 1, with output $[b]$. It reaches the verification-return state with that bit stored in the auxiliary tape, within $3T_v+|x|+1+8$ steps. If $b$ is true, one further step halts and writes the output bit; this is the acceptance transition described by `enumCont_body_accept`. If $b$ is false, the rejection transition moves to the increment phase at state $q_i$, preserving the seam word. Apply the body-increment result using the assumed halting computation from $q_i$; it reaches the anchor with the fixed-width increment, or the original word on overflow. Concatenate these runs using the run-addition law and the one-step successor law. The call, rejection, increment, and final-step costs sum to at most $3T_v+3T_i+2|x|+3|s|+21$, as required.

**Key facts.** `Complexity.enumCont_body_call`, `Complexity.enumCont_body_accept`, `Complexity.enumCont_body_increment`, `Complexity.enumCont_body_reject`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
