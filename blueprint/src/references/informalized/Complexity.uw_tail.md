<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.uw_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output of the query routine

**Claim.** Starting from the designated query configuration with buffer $u$, the machine run using choices $b_1,b_2$ halts and outputs $[1]$ if $u\in B$, and $[0]$ otherwise.

**Proof.** The query configuration’s query tape contains exactly $u$, so its query string is $u$ (`Turing.OracleTM.queryString_bufferTape`). Expand the two-step run into its successive steps, using the run equations for a cons and for the empty choice list (`Turing.OracleNDTM.runWith_cons`, `Turing.OracleNDTM.runWith_nil`). The first step, in the query state, branches according to whether the query string belongs to $B$ (`Turing.OracleTM.step_of_qQuery`). If $u\in B$, the machine enters its positive-answer state; otherwise it enters its negative-answer state. In either case, the second step applies the corresponding answer action: the machine halts and appends the associated bit to the output (`Turing.OracleTM.step_of_answerAction`). The choice-specific machine steps agree with the steps of the machine having that choice fixed (`Turing.OracleNDTM.stepWith_eq_fixChoice_step`). Since the initial output is empty, the final output is the singleton containing the membership bit, and the final state is halted.

**Key facts.** `Turing.OracleTM.queryString_bufferTape`, `Turing.OracleNDTM.runWith_cons`, `Turing.OracleNDTM.runWith_nil`, `Turing.OracleNDTM.stepWith_eq_fixChoice_step`, `Turing.OracleTM.step_of_qQuery`, `Turing.OracleTM.step_of_answerAction`.
