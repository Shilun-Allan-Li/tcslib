<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Length Computation Time

**Claim.** The finite Turing machine computes the binary expansion of the length of every finite input word $x$ in time $5(|x|+1)$.

**Proof.** Fix an input $x$. The counter-count result supplies a time $t$ at which the machine has reached state $0$ with the binary digits of $|x|$ on its tape, and bounds $t+2|x|.	ext{bits.count}(	ext{true})$ by $4|x|$. One further step takes the machine from state $0$ into the emission state without changing the counter tape. The run-length composition law then places it in that state at time $t+1$. The emission result says that after a further $|x|.	ext{bits.length}+1$ steps the machine halts with those bits as output. Hence it computes the desired output in time $(t+1)+(|x|.	ext{bits.length}+1)$. Finally, the bound on the length of a natural number's bit list, together with the counter-count time bound, shows this time is at most $5(|x|+1)$. The monotonicity of computation time extends the computation to that stated time.

**Key facts.** `Turing.FinTM.f2_counter_count`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_counter_emit`, `Turing.MultiTapeTM.runFrom_add`, `Turing.length_bits_le_self`, `Turing.FinTM.ComputesInTime.mono`.
