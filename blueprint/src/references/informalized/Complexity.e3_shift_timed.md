<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_shift_timed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Running Time of the Zero-Prefixing Machine

**Claim.** For every fixed binary word $w$, the machine with no work tapes computes on every binary input $x$ the word of $|x|$ zero bits followed by $w$ in exactly $(|w|+2)(|x|+1)$ steps.

**Proof.** Fix an input $x$. The exact computation result gives the required output and halting time $|x|+|w|+2$ (`Complexity.e3_shift_computes`). This time is at most $(|w|+2)(|x|+1)$: expanding the latter and using nonnegativity of the lengths verifies the inequality. Computation in time is preserved when the time bound is increased (`Turing.FinTM.ComputesInTime.mono`), so the machine computes the same output at the stated bound. Since $x$ was arbitrary, this holds for every input.

**Key facts.** `Complexity.e3_shift_computes`, `Turing.FinTM.ComputesInTime.mono`.
