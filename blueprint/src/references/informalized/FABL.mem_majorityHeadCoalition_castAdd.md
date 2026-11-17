<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.mem_majorityHeadCoalition_castAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Head coalition membership under cast addition

**Claim.** For $i\in\{0,\ldots,k-1\}$, the index obtained by placing $i$ in the first summand belongs to the coalition of the first $k$ indices in a set of size $k+m$.

**Proof.** The canonical identification of the disjoint union sends the left-summand index $i$ to the index obtained by cast addition. The left-summand membership result says that this identified index belongs to the head coalition ( `FABL.mem_majorityHeadCoalition_left` ). Rewriting the cast-added index using that identification gives the desired membership.

**Key facts.** `FABL.mem_majorityHeadCoalition_left`.
