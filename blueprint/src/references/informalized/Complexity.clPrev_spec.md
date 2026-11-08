<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPrev_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of the Last Previous Visit

**Claim.** If the last previous visit to tape $\tau$’s position at time $t$ occurs at time $s$, then $s<t$, the two head positions agree, and every earlier time with that same position is at most $s$.

**Proof.** By definition, the previous-visit option is the maximum, if one exists, of the times in $[0,t)$ whose head position equals the position at time $t$. The characterization of a maximum list element (`List.max?_eq_some_iff`) therefore gives that $s$ belongs to this filtered list and is at least every other member. Membership says both that $s<t$ and that the head positions at $s$ and $t$ agree. Any $r<t$ with the same head position is also a member of the filtered list, so maximality gives $r\le s$.
