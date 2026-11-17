<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_findClock_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Least Event Time

**Claim.** If the machine first reaches either the read state with no stored Boolean value or the exit state at a positive time $t$, then the clock defined as the least positive such event time equals $t$.

**Proof.** The event at time $t$ shows that the set of positive event times is nonempty, so the clock's definition selects its least element. The hypothesis rules out either event at every positive time strictly less than $t$. Thus no smaller positive time belongs to the set, while $t$ itself does; by the defining property of the least natural number in a nonempty set, the selected time is $t$.
