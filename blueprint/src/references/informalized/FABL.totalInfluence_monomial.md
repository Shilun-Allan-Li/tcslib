<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/Basic.lean :: FABL.totalInfluence_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial Total Influence

**Claim.** For any finite set $S$ of coordinates, the total influence of its monomial is $|S|$.

**Proof.** For each coordinate $i$, the monomial has influence $1$ if $i\in S$ and $0$ otherwise (`FABL.influence_monomial`). Summing these coordinate influences therefore counts exactly the elements of $S$, giving total influence $|S|$.

**Key facts.** `FABL.influence_monomial`.
