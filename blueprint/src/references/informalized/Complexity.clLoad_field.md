<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLoad_field -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loading One Row Field

**Claim.** For a chosen field, the row loader reaches a configuration with that field replaced by the encoded word, the index advanced by one, and the stream cursor advanced by the encoding length, within the stated positive time bound.

**Proof.** First run the two-tape fresh-field routine on the selected field and the stream beginning with the chosen encoding. Its completion result (`clFresh_first`) gives a time at most $2|old_i|+3|word|+6$ and identifies the resulting reader configuration, including its new cursor position. The routine does not enter its completion control before that time. The placement lemma (`clLoad_frame`) identifies the row loader’s current tapes with the two-tape routine’s tapes embedded in the slots for field $i$ and the stream. The simulation result for placed machines (`clPlaced_run`) therefore transfers the run to the row loader for the same number of steps; its guard is satisfied because the fresh routine has not yet reached its completion control. Applying the frame identification again gives the row configuration with field $i$ replaced by `word`. One further row-loader step detects that completion control and advances the field index, leaving the tape contents and cursor fixed. Thus the total time is $t+1$, positive and bounded by $2|old_i|+3|word|+7$, and it yields the required configuration.

**Key facts.** `Complexity.clFresh_first`, `Complexity.clLoad_frame`, `Complexity.clPlaced_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
