<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkPad.lean :: Randomized.padNbr_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padded neighbor characterization

**Claim.** For distinct $u,v$, the padded neighbor of $u$ at slot $i$ equals $v$ exactly when the natural-number index of $i$ equals the value of $v$ and $r(u,v)$ holds.

**Proof.** Unfold the padding rule and split according to whether the slot index is below $n$, and, when it is, whether the relation holds at the corresponding vertex. If the index is below $n$ and the relation holds, the padded neighbor is precisely the vertex represented by that index. Equality with $v$ therefore forces equality of their natural-number values, and the relation at the indexed vertex is then $r(u,v)$. Conversely, equality of those values identifies the indexed vertex with $v$, so the padded neighbor is $v$. If the index is below $n$ but the relation fails, or if it is not below $n$, the padded neighbor is $u$; it cannot equal the distinct vertex $v$. In the first of these cases the proposed right-hand condition would identify the indexed vertex with $v$, making the assumed relation exactly the one that was split as false. In the second case that index equality would imply that the value of $v$ is below $n$, contradicting the slot's being outside the range.
