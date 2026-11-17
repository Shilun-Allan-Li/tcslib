<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.NDTM.abs_runWith_workTapePos_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-tape displacement bound

**Claim.** For any work tape, the absolute change in its head position over a run under a finite choice word is at most the length of that word.

**Proof.** Proceed by induction on the choice word, allowing the starting configuration to vary. The empty word leaves the configuration unchanged, so the displacement is zero. For a word beginning with a choice $b$, the run first takes one step under $b$ and then runs the remaining word. By the induction hypothesis, the remaining run moves the head by at most the length of that remaining word. The first step moves the selected work-tape head by either $-1$, $0$, or $1$ if the configuration is active; hence its displacement has absolute value at most $1$. If the configuration is halted, the step leaves it unchanged and the same bound holds. The triangle inequality now bounds the total displacement by $1$ plus the length of the remaining word, which is the length of the full word.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.NDTM.stepWith_of_halt`, `Turing.NDTM.stepWith_of_state`, `Turing.signType_bounds`.
