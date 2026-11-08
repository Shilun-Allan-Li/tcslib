<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalk.lean :: Complexity.plainAt_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Plain prefix after its first bit

**Claim.** The condition that $x$ agrees with $b::u$ starting at position $r$ and has length $r+|b::u|$ is equivalent to the conjunction that $x_r=b$ (using false for an out-of-range entry) and that $x$ agrees with $u$ starting at position $r+1$ and has length $(r+1)+|u|$.

**Proof.** Unpack the agreement and length conditions for $b::u$. In the forward direction, the agreement at index zero gives $x_r=b$. For each later index, write it as $i+1$; the list lookup identity for the tail of a cons shows that the agreement is exactly the agreement of $x$ with $u$ at position $r+1$. The length equation reduces to the corresponding equation for $u$ after removing the first bit. Conversely, the agreement at index zero follows from $x_r=b$. Every positive index is $i+1$, and the same lookup identity reduces its agreement to the assumed agreement with $u$ at position $r+1$. The length condition follows from the assumed length equation for the tail and $|b::u|=1+|u|$.
