<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Segment.time_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of a first hitting time

**Claim.** If two runs from $a$ each avoid $F$ strictly before their respective endpoints, and each endpoint state belongs to $F$, then their endpoint times are equal.

**Proof.** Compare $t$ and $t'$ by trichotomy. If $t<t'$, the first endpoint equation identifies the state at time $t$ with $b$; since $b$'s state belongs to $F$, the run is in $F$ at time $t$. But the second segment avoids $F$ at every time strictly before $t'$, including time $t$, a contradiction. If $t'>t$, the same argument with the segments exchanged contradicts the first segment's avoidance condition. The only remaining case is $t=t'$.
