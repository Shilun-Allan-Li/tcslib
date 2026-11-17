<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.CodeTM.one_le_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Space Usage

**Claim.** For every code-normal-form machine, binary input, and time, the machine's total work-tape space usage from its initial configuration is at least $1$.

**Proof.** Choose the unique work tape, indexed by $i_0$. Its head has visited a position by time $t$: the visited-position set includes the head position at time $0$, since $0$ belongs to the range of times from $0$ through $t$. Thus this set is nonempty and has cardinality at least $1$. The total space usage is at least the space usage of this tape, so it too is at least $1$.

**Key facts.** `Turing.MultiTapeTM.spaceUsedByTape_le_spaceUsed`.
