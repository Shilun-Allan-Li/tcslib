<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.SafeSegment.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Safe Segments

**Claim.** If there is a safe segment from $a$ to $b$ of length $t$ and a safe segment from $b$ to $c$ of length $v$, relative to the same forbidden set and position predicate, then there is a safe segment from $a$ to $c$ of length $t+v$.

**Proof.** Discard the endpoint-avoidance components temporarily and concatenate the two underlying segments using the segment concatenation result (`Turing.Segment.trans`). This gives a segment from $a$ to $c$ of length $t+v$ with the required avoidance and position conditions. The second safe segment already asserts that $c$'s state lies outside the forbidden set, supplying the endpoint condition for the concatenated safe segment.

**Key facts.** `Turing.Segment.trans`.
