<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Basic.lean :: Turing.FinTM.computesInSpace_zero_of_k_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero space with no work tapes

**Claim.** If a finite Boolean-alphabet Turing machine has no work tapes and halts with output $f(x)$ on every input $x$, then it computes $f$ using space bounded by zero on every input.

**Proof.** Fix an input $x$. By hypothesis, choose a time $t$ at which the machine computes $f(x)$. With zero work tapes, the space used at any time is zero (`spaceUsed_zero_tapes_eq_zero`). Hence the chosen computation has space at most zero, which is exactly the required space bound for this input. Since $x$ was arbitrary, the machine computes $f$ in zero space on every input.

**Key facts.** `Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero`.
