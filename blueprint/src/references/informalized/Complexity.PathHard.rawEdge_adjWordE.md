<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.rawEdge_adjWordE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency Word Encodes Edges

**Claim.** For vertices $u,v$, the raw adjacency relation of the listed edge indicators holds exactly when $u<n$, $v<n$, and there is an edge from $u$ to $v$ at parameter $s$.

**Proof.** Unfold the raw adjacency relation. In either direction, the bounds $u<n$ and $v<n$ imply $un+v<n^2$, so the relevant position lies in the listed adjacency word. Its value is the indicator of the edge at the quotient and remainder of that position (`adjWordE_getD`). Since $v<n$, division of $un+v$ by $n$ has quotient $u$ and remainder $v$. Thus the stored bit is precisely the indicator of the edge from $u$ to $v$. A true indicator is equivalent to the edge proposition, giving both implications.

**Key facts.** `Complexity.PathHard.adjWordE_getD`.
