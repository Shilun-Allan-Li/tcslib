<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.slots_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exhaustion of the combined indices

**Claim.** Every index in the combined set belongs to the first block, the second block, or the singleton final block; hence the three hypotheses imply that $P$ holds at every index.

**Proof.** Apply the finite-index decomposition first to separate an arbitrary index into the initial block of size $s+a$ or the final singleton. In the initial block, decompose again into the first block of size $s$ or the second block of size $a$. The resulting cases are precisely indices of the forms $sI(i)$ and $aI(i)$, where the assumptions give $P$. In the singleton case its index is necessarily zero within that block, since a singleton type has only one element; this is the index $yI$, where $P$ holds by hypothesis.
