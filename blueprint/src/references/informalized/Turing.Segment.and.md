<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.and -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Combining Segment Invariants

**Claim.** If the same run is a segment relative to $F$ and $P$, and also relative to $F$ and $Q$, then it is a segment relative to $F$ and the predicate $p\mapsto P(p)\land Q(p)$.

**Proof.** Keep the endpoint equality and the avoidance of $F$ from the segment relative to $P$. At each time $u\le t$, the first segment supplies $P$ for the head-position vector, and the second supplies $Q$ for that same vector. Pairing these assertions gives the conjunction required at every such time.
