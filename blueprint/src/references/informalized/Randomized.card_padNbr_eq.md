<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkPad.lean :: Randomized.card_padNbr_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count of Padded Neighbors

**Claim.** For distinct vertices $u,v$ and $n\le D$, the number of indices among the first $D$ whose padded neighbor of $u$ is $v$ is one when $r(u,v)$ holds and zero otherwise.

**Proof.** For every index $i$, the padded-neighbor characterization (`padNbr_eq_iff`) says that the padded neighbor equals $v$ exactly when $i=v$ and $r(u,v)$ holds. If the relation holds, the unique qualifying index is the element $v$ viewed in the larger index set of size $D$; this is available because $v<n\le D$. The filtered set is therefore a singleton and has cardinality one. If the relation does not hold, the characterization shows there are no qualifying indices, so the cardinality is zero.

**Key facts.** `Randomized.padNbr_eq_iff`.
