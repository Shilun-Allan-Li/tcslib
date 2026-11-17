<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.tail_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting in the Tail Phase

**Claim.** Starting at tail position zero with register values given by a state whose registers are bounded by $B$, the program halts with answer determined by the tail value at the current index; every configuration before halting satisfies the guard.

**Proof.** Write the tail phase position as $j$ and the remaining counter as $r$. We prove by induction on $r$, allowing any $j$ and assuming $r\le i$, that starting at position $j$ with counter $r$ halts with answer given by the tail value at index $j+r$. For $r=0$, the program tests the current position and immediately answers the corresponding tail value. For $r+1$, if $j<4$, it decrements the counter and advances to position $j+1$. The induction hypothesis then applies, since $r\le i$, and the resulting index satisfies $j+1+r=j+(r+1)$. If $j\ge4$, the program takes the out-of-range branch and answers false; the tail value at $j+r+1$ is also false because that index is at least five. Each transition preserves the required register bound and instruction precondition, as ensured by the bounded-state hypothesis. Applying the induction result with $j=0$ and $r=i$ gives the stated halt and answer.

**Key facts.** `Complexity.PathHard.stepH_of`, `Complexity.PathHard.ans_halt`.
