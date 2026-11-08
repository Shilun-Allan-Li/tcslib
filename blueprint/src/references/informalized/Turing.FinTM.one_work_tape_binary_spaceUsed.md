<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.one_work_tape_binary_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary One-Tape Simulation with Space Bound

**Claim.** A machine computing a function within time $T$ and using at most $S(|x|)$ space on every input and at every time can be replaced by a one-work-tape simulation over the binary alphabet with quadratic time and linear-in-$S(|x|)+1$ space bounds.

**Proof.** Apply the one-tape simulation with a space bound to obtain a machine over an enlarged alphabet. It preserves the function on encoded inputs, has one work tape, runs within $c_1(T(n)+1)^2$, and uses at most $c_1(S(n)+1)$ space (`Turing.FinTM.one_work_tape_spaceUsed`). Reduce its alphabet back to binary. The reduction preserves the number of work tapes and gives a new constant $c_2$; its time bound becomes $c_2(c_1(T(n)+1)^2+1)$ and its space bound becomes $c_2(c_1(S(n)+1)+1)$ (`Turing.FinTM.alphabet_reduction_spaceUsed`). For either nonnegative quantity $u=(T(n)+1)^2$ or $u=S(n)+1$, we have $u\ge1$, so $c_1u+1\le(c_1+1)u$. Both bounds are therefore covered by the single constant $c_2(c_1+1)$, and the resulting machine still has one work tape.

**Key facts.** `Turing.FinTM.one_work_tape_spaceUsed`, `Turing.FinTM.alphabet_reduction_spaceUsed`.
