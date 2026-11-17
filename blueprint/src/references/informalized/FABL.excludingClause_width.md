<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.excludingClause_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of the excluding clause

**Claim.** For every sign assignment on $r$ coordinates, the clause constructed from it has width $r$.

**Proof.** The clause has one literal for each index in the list of all $r$ coordinates. That list has length $r$, and mapping it to the corresponding literals preserves its length. Since the width is the number of literals, the clause has width $r$.
