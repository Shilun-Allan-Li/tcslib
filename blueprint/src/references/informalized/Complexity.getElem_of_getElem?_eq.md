<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.getElem_of_getElem?_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optional lookup gives an indexed entry

**Claim.** If optional lookup of $w$ at index $i$ returns $v$, then $i$ is within the length of $w$ and the entry of $w$ at index $i$ equals $v$.

**Proof.** The characterization of successful optional list lookup states that $w[i]? = \operatorname{some}(v)$ holds exactly when $i < w.length$ and the indexed entry is $v$. Applying its forward implication to the hypothesis gives both conclusions.
