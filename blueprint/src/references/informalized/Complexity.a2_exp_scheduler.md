<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a2_exp_scheduler -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential unary scheduler

**Claim.** For all natural numbers $C,c$, there are a finite deterministic Turing machine $S$ over the Boolean alphabet and a natural number $B$ such that, on every Boolean input $x$, the machine outputs $C\cdot 2^{(|x|+1)^c}$ ones within the stated polynomial in $|x|+C\cdot 2^{(|x|+1)^c}+1$.

**Proof.** Choose a machine $E$ that writes the binary digits of $R=C\cdot 2^{(|x|+1)^c}$ in time at most $A(|x|+1)^{c+1}$, supplied by the timed exponential-bits construction (`e3_exp_bits_timed`). Compose it with the decoder that, on the binary representation of a number, writes that many ones (`a2Value_bits`, `a2_decode_computes`). The buffered composition first runs $E$, spends at most $|\mathrm{bits}(R)|+2$ steps to transfer its output, and then runs the decoder. Since the output length of a machine is at most its running time (`output_length_le`), the binary word has length at most $A(|x|+1)^{c+1}$. The decoder’s stated time bound and the composition simulation (`bufferedComp_start`, `bufferedSecondCfg_run`, and `runFrom_add`) therefore give the desired output in at most $a+T$ steps, where $a$ is the first phase and transfer time and $T=2|\mathrm{bits}(R)|+2+(R+1)(2|\mathrm{bits}(R)|+3)$ is the decoder time. Put $P=(|x|+1)^{c+1}$ and $m=|x|+R+1$. Then $1\le P$, $P\le m^{c+1}$, and $R+1\le m$, so $(R+1)P\le m^{c+2}$. The bounds on the first phase and each decoder round give $a+T\le(6A+7)(R+1)P$, hence at most $(6A+7)m^{c+2}$. Taking $B=6A+7$ and using monotonicity of the running-time bound yields the claim (`ComputesInTime.mono`).

**Key facts.** `Complexity.e3_exp_bits_timed`, `Complexity.a2Value_bits`, `Complexity.a2_decode_computes`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.bufferedComp_start`, `Turing.FinTM.bufferedSecondCfg_run`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
