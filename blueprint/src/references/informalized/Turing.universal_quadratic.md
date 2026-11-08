<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.universal_quadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic Universal Simulation

**Claim.** A single binary finite-tape machine simulates any machine computing a function within time $T$, on the paired encoding of a fixed code and an input, within a constant multiple of $(T(|x|)+1)^2$ steps.

**Proof.** Fix the effective coding scheme and take the universal machine supplied by the universal simulation theorem (`Turing.universal`). Given a machine $M_0$, function $f$, time bound $T$, and a proof that $M_0$ computes $f$ within that bound, first replace $M_0$ by an equivalent one-work-tape binary machine $M_1$. The one-tape simulation theorem supplies a constant $c_1$ such that $M_1$ computes $f$ on each input within $c_1(T(|x|)+1)^2$ steps (`Turing.FinTM.one_work_tape_binary`). Encode $M_1$ as a coded machine $N$ preserving its computations, then use the fixed code string $\alpha$ obtained by encoding $N$ (`Turing.exists_codeTM`). The coding law says decoding this string recovers $N$ (`Turing.MachineCode.decode_encode`), so the universal simulation theorem gives a time bound $C_U(c_1(T(|x|)+1)^2+1)$ for the universal machine. Since $(T(|x|)+1)^2\ge 1$, this is at most $C_U(c_1+1)(T(|x|)+1)^2$. Monotonicity of computation in the time bound then yields the result with constant $C=C_U(c_1+1)$ (`Turing.FinTM.ComputesInTime.mono`).

**Key facts.** `Turing.universal`, `Turing.FinTM.one_work_tape_binary`, `Turing.exists_codeTM`, `Turing.MachineCode.decode_encode`, `Turing.FinTM.ComputesInTime.mono`.
