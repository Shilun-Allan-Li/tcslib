<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.plainAt_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of a plain segment

**Claim.** The condition that $x$ agrees with $u$ starting at position $r$ and has length $r+|u|$ is equivalent to $r\le |x|$ and $x$ with its first $r$ entries deleted being $u$.

**Proof.** Suppose first that $x$ agrees with $u$ at the specified positions and has length $r+|u|$. The length equation gives $r\le |x|$. The lists $x$ with its first $r$ entries deleted and $u$ have equal lengths. At every index in that range, the lookup identity for a dropped list identifies its entry with the entry of $x$ at position $r+i$; the assumed agreement makes this equal to the corresponding entry of $u$. Equality of lists follows from equality of lengths and entries (ext_getD'). Conversely, suppose $r\le |x|$ and the dropped list equals $u$. The same lookup identity transfers agreement of the dropped list with $u$ to agreement of $x$ with $u$ starting at $r$. The length of the dropped list is $|x|-r$, so the assumed bound on $r$ gives the required length equation.

**Key facts.** `Complexity.ext_getD'`, `Complexity.getD_drop`.
