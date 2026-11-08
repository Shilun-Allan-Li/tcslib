<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.perfectMatchingPartnerPerm_cycleType -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cycle Type of the Matching Permutation

**Claim.** For every natural number $m$ and every perfect matching of the complete graph on $2m$ vertices, the associated permutation has cycle type consisting of exactly $m$ cycles of length $2$.

**Proof.** Write $\sigma$ for the matching partner permutation. Since matching partners are mutual, applying $\sigma$ twice fixes every vertex, so $\sigma^2=1$ (`perfectMatchingPartner_involutive`). The cycle type theorem for a permutation whose square is the identity says its cycles have lengths dividing the prime $2$; thus every cycle has length $1$ or $2$. No vertex is fixed, because a vertex is not its own matching partner (`perfectMatchingPartner_ne`). Hence every cycle has length $2$. The support is therefore all $2m$ vertices, and the sum of the cycle lengths is $2m$. If there are $k$ cycles, this gives $2k=2m$, so $k=m$.

**Key facts.** `FABL.perfectMatchingPartner_involutive`, `FABL.perfectMatchingPartner_ne`.
