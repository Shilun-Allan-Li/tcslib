<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean :: Complexity.LogProg.indicator_eq_decide -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator and membership decision

**Claim.** For any set $S$ and element $a$, the Boolean indicator of $S$ at $a$ equals the Boolean decision for the proposition $a\in S$.

**Proof.** By definition, the indicator returns `true` when $a\in S$ and `false` otherwise. The Boolean decision for $a\in S$ has exactly the same two cases, so the two values agree.
