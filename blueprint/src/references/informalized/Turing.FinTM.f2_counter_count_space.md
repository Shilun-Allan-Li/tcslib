<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_count_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Space Bound During Counting

**Claim.** For every finite Boolean word $x$ and every $i\le |x|$, there is a time $t$ satisfying the counting time bound and reaching the prescribed counter configuration, such that at every time $u\le t$ the work-tape head lies between $-2(\mathrm{size}(|x|)+1)$ and $2(\mathrm{size}(|x|)+1)$.

**Proof.** Induct on $i$, strengthening the counting assertion to include the head-position bound at every earlier time. At $i=0$, take time zero; the initial head is at $0$, within the stated interval. For the successor step, use the induction hypothesis to reach the configuration storing $i.bits$ at time $t$. The increment procedure reaches the configuration for $i+1$ after a further $2\,\mathrm{carry}(i.bits)+2$ steps (`f2_counter_increment`), and the binary increment identity and its true-bit potential identity (`f2_counterInc_bits`, `f2_counterInc_potential`) establish the time bound. For times through $t$, retain the induction hypothesis. For a later time $u$ up to the new endpoint, compose the run at time $t$ with the remaining run (`runFrom_add`). The head can move by at most one cell per step, so its position differs from its starting value $0$ by at most the elapsed number of steps (`f2_head_steps`). This remaining duration is bounded by the length of the incremented binary word: the increment length and carry bound (`f2_counterInc_length`), and the fact that binary representations have length at most the size bound for $|x|$ (`Nat.size_eq_bits_len`, with monotonicity of size), put the head within the claimed interval. The arithmetic combining these bounds gives both endpoints.

**Key facts.** `Turing.FinTM.f2_counterInc_bits`, `Turing.FinTM.f2_counterInc_potential`, `Turing.FinTM.f2_counter_increment`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_head_steps`, `Turing.FinTM.f2_counterInc_length`.
