<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.prevVisit_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A previous visit occurs earlier

**Claim.** If the last previous visit of tape $\tau$ at time $t$ is $s$, then $s<t$.

**Proof.** A maximum of a filtered finite list, when defined, is a member of that list. Thus $s$ belongs to the list of times below $t$ whose head position agrees with the head position at time $t$. Membership in the range list gives $s<t$.
