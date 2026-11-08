<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyRun.lean :: Randomized.Amplify.abs_workTapePos_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Position Bound

**Claim.** If the total number of work-tape positions visited by a nondeterministic machine during a run is at most $S$, then the absolute value of the final head position on each work tape is at most $S$.

**Proof.** Fix a work tape and let $p(j)$ be its head position after the machine has processed the first $j$ choices. Initially $p(0)=0$. At each step the head moves by at most one position (`workTapePos_apply_le`); after the choice word ends, the configuration remains fixed. The run decomposition facts (`runWith_append`, `runWith_cons`, and `runWith_nil`) identify these successive positions with the run on each prefix, so the unit-step bound applies to the entire sequence.

The final position occurs among the positions traced by these prefixes. The unit-step counting lemma `abs_lt_card_image_of_unitSteps` therefore bounds its absolute value strictly by the number of distinct visited positions on this tape. That number is at most the total space used: the total is the sum of the visited-position counts over all tapes, and the fixed tape's count is one nonnegative summand. Since total space is at most $S$, the strict bound in particular implies that the absolute value is at most $S$.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`, `Turing.workTapePos_apply_le`, `Turing.MultiTapeTM.ConfigCount.abs_lt_card_image_of_unitSteps`.
