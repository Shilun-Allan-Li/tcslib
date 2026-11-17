<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dgWindow_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Window Width Bounded by Space

**Claim.** If a positive-width window satisfies the stated head, blankness, visitation, size, and history conditions, then its width is at most the total space used through time $t$.

**Proof.** Take the finite union of the sets of positions visited by each work-tape head through time $t$. Every integer in the window belongs to this union: for an integer $j$ with $a\le j<a+n$, the visitation hypothesis supplies a tape head and a time $u\le t$ at which that head is at $j$. The window’s integer coordinates are precisely the integer interval from $a$ through $a+n-1$, whose cardinality is $n$ (`Int.card_Icc`). Its cardinality is therefore at most that of the union. The union bound for finite unions bounds the latter by the sum of the cardinalities of the individual visited-position sets, which is exactly the total space used. Hence $n$ is at most that total.
