<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/ModelInvariance.lean :: Complexity.mem_P_iff_one_work_tape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time with One Work Tape

**Claim.** A language belongs to $\mathsf{P}$ exactly when a finite Turing machine with one work tape decides it within $C(n+1)^d$ steps for natural numbers $C,d$.

**Proof.** For the forward direction, first express membership in $\mathsf{P}$ using a conventional polynomial running-time bound (`Complexity.mem_P_iff`). Apply the one-work-tape simulation theorem (`Turing.FinTM.one_work_tape_binary`) to the machine's decision function. It gives an equivalent one-work-tape machine running in time at most a constant multiple of $(C(n+1)^d+1)^2$. Because $(n+1)^d\ge1$, we have $C(n+1)^d+1\le(C+1)(n+1)^d$. Squaring and absorbing the factor into the constant yields a bound of the form $C'(n+1)^{2d}$; time monotonicity extends the computation to that bound. Conversely, any one-work-tape machine satisfying such a polynomial bound is already a finite Turing machine with a polynomial time bound, so `Complexity.mem_P_iff` gives membership in $\mathsf{P}$.

**Key facts.** `Complexity.mem_P_iff`, `Turing.FinTM.one_work_tape_binary`, `Turing.FinTM.ComputesInTime.mono`.
