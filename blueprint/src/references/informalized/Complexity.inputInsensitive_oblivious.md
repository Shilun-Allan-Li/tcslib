<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean :: Complexity.inputInsensitive_oblivious -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-Insensitive Machines Are Oblivious

**Claim.** If replacing every present input symbol by the fixed symbol $z$ leaves every transition unchanged, then equal-length inputs yield identical input-head and work-tape head positions at every time.

**Proof.** Consider the machine `maskedClock` associated with $P$ and $z$. Its transition function applies $P$’s transition to the input symbol after replacing each present symbol by $z$. The hypothesis says this transition agrees with $P$’s transition for every state, input symbol, and tuple of work-tape reads. Hence the masked-clock machine is exactly $P$. The masked-clock obliviousness result (`maskedClock_oblivious`) says that its head positions depend only on the input length and time. Applying it to the same machine $P$ proves the asserted equality for any two equal-length inputs.

**Key facts.** `Complexity.maskedClock_oblivious`.
