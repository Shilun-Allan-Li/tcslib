<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.one_work_tape_binary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary One-Tape Simulation

**Claim.** If a finite Turing machine over the binary alphabet computes a function within time $T$, then another finite machine over the binary alphabet with exactly one work tape computes the same function within a bound of the form $c(T(n)+1)^2$.

**Proof.** First apply the one-work-tape simulation theorem. It gives a machine over a finite enlarged alphabet, an encoding of binary symbols into that alphabet, and a constant $c_1$ with time bound $c_1(T(n)+1)^2$ (`Turing.FinTM.one_work_tape`). Then apply alphabet reduction to return to the binary alphabet. This gives a binary machine with the same number of work tapes and a time bound $c_2(c_1(T(n)+1)^2+1)$ (`Turing.FinTM.alphabet_reduction`). The work-tape count is therefore still one. Since $(T(n)+1)^2\ge 1$, we have $c_1(T(n)+1)^2+1\le(c_1+1)(T(n)+1)^2$. Thus the claimed bound follows with $c=c_2(c_1+1)$, using monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.one_work_tape`, `Turing.FinTM.alphabet_reduction`, `Turing.FinTM.ComputesInTime.mono`.
