<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2Borrow_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Borrow Scan Computation

**Claim.** For each prefix and suffix, starting in the borrow state with the head at the prefix boundary and tape contents $\mathrm{pre}\,u$, after $\beta(u)+1$ steps the machine carries the fixed-width decrement's success flag, has the decremented word after the prefix, and has head at $|\mathrm{pre}|+\beta(u)-1$, while preserving the input position and output.

**Proof.** Induct on the suffix $u$, proving the claim for every prefix. For the empty suffix, one borrow transition enters the result state with failure, as described by the single-step rule (`a2Borrow_step`); this is exactly the claimed configuration after one step. If $u$ begins with $1$, the same rule flips that bit to $0$, reports success, and moves left; this gives the claim in one step, with the tail unchanged. If $u$ begins with $0$, the rule flips it to $1$, moves right, and stays in the borrow state. The remaining suffix is then processed with the enlarged prefix $\mathrm{pre}\,1$. Apply the induction hypothesis to that suffix and prefix, and concatenate the first transition with the resulting run. The recursive definitions of borrow position and decrement, together with list concatenation and integer arithmetic, identify the final tape, flag, and head position. Each transition leaves the input position and output unchanged.

**Key facts.** `Complexity.a2Borrow_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
