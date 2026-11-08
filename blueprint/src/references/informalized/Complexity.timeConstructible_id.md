<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/TimeConstructible.lean :: Complexity.timeConstructible_id -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity Is Time Constructible

**Claim.** The identity function on the natural numbers is time constructible: it dominates each input length and a finite binary Turing machine outputs the binary representation of the input length within a constant multiple of that length plus one.

**Proof.** The identity function dominates $n$ by equality. For the machine, use the length-counting machine. The counter-counting result says that on input $x$, it reaches the counter configuration for $|x|$ in some $t$ steps with $t+2|x|.bits.count(true)\le 4|x|$ ( `counter_count` ). One additional step enters the emission state, as verified by the transition at the input boundary. From that state the emission result says that in $|x|.bits.length+1$ further steps the machine halts with output $|x|.bits$ ( `counter_emit` ). Decomposing the run into these phases gives total time $(t+1)+(|x|.bits.length+1)$. Since the bit-list length is at most its represented number ( `length_bits_le_self` ), the displayed count bound implies this total is at most $5(|x|+1)$. The computation therefore meets the time-constructibility bound with positive constant $5$; if necessary, `ComputesInTime.mono` extends the computation to the specified bound.

**Key facts.** `Complexity.counter_count`, `Complexity.counter_emit`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Turing.length_bits_le_self`, `Turing.FinTM.ComputesInTime.mono`.
