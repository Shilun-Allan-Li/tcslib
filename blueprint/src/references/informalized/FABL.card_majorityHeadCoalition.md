<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.card_majorityHeadCoalition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority head coalition size

**Claim.** For natural numbers $k$ and $m$, the set of the first $k$ coordinates in $[k+m]$ has cardinality $k$.

**Proof.** The majority head coalition is the image of all $k$ indices under the embedding of the first summand into the disjoint union of sets of sizes $k$ and $m$, identified with $[k+m]$. An embedding is injective, so its image has the same cardinality as its domain. The domain has cardinality $k$, proving the claim.
