<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.maxLayer1RestrictedWidth_le_blocked -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Width and Blocked Width

**Claim.** For any depth circuit and coordinate restriction, the maximum first-layer restricted width is at most five times the maximum blocked restricted width, plus four.

**Proof.** Fix a first-layer gate index $i$. Its blocked restricted width is at most the maximum blocked restricted width, since that maximum is the supremum over all first-layer indices. By definition, the blocked width is the restricted width divided by $5$. For natural numbers, if $a/5\leq b$, then $a\leq 5b+4$; applying this to the gate at $i$ bounds its restricted width by five times the maximum blocked width plus four. Since this bound holds for every first-layer index, it also bounds their supremum. If there are no such indices, the supremum has its empty-set value $0$, and the stated bound holds as well.
