<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_seed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seeding the Main Stack

**Claim.** From the scanning state at input-head position $|x|+1$ with empty stacks and output, exactly three steps reach the backward-reading state at position $|x|$, with the sentinel bit and terminator on the main stack and all other stacks and the output empty.

**Proof.** Expand the three-step run into its successive transitions, using the run recurrence and the zero-step identity (`runFrom_succ_eq_step'`, `runFrom_zero`). At the end of the input, the input symbol is absent. The scanning transition therefore moves left into the state that starts the terminator; that state pushes the terminator onto the main stack and moves left again. The next state pushes the sentinel bit and enters the backward-reading state. The input head is unchanged during both pushes and moves left once during each of the first and third transitions, so its final position is $|x|$. On the stack representation, each push writes the new symbol just before the existing word; applying the stack-push identity twice (`bridgeStack_push`), with the tape assignment localized to the main stack (`bridgeStore_at`), gives the word consisting of the sentinel bit and terminator. The left- and zero-movement facts (`moveInputPos_neg_of_ne_left`, `moveInputPos_zero`) verify the head positions; the transition specification is expressed by `bridge_step`.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.bridgeStack_push`, `Turing.bridgeStore_at`, `Turing.bridge_step`, `Turing.moveInputPos_neg_of_ne_left`, `Turing.moveInputPos_zero`.
