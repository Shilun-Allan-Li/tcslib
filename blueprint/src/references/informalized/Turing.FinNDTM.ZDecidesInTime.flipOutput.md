<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.ZDecidesInTime.flipOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementation by flipping output

**Claim.** Complementing each output bit preserves the total nonhalting bound and makes every halted run output the indicator of the complement language.

**Proof.** Fix an input $x$. For each choice word and each horizon, the flipped machine's run returns the original run's result with its output list bitwise complemented (`haltRun_flipOutput`). In particular, its result is `none` exactly when the original result is `none`; hence the nonhalting events agree for every choice word. Their probabilities, and therefore every partial sum in the total nonhalting bound, are equal by invariance of `randProb` under pointwise equivalent events (`randProb_congr`). Now consider any halted run. Its flipped result must be some output, and the correspondence above identifies that output as the bitwise complement of an original halting output. The original correctness hypothesis says that output is the one-symbol indicator of membership in $L$ (`haltRun_eq_some_iff` translates this into halting and output conditions). If $x\in L$, flipping the indicator gives false, the indicator of $x\notin L$; if $x\notin L$, it gives true. Thus the flipped machine has the required output on every halted run.

**Key facts.** `Turing.FinNDTM.haltRun_flipOutput`, `Randomized.randProb_congr`, `Turing.FinNDTM.haltRun_eq_some_iff`.
