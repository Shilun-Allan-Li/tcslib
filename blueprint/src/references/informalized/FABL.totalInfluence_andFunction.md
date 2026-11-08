<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/Basic.lean :: FABL.totalInfluence_andFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# AND Total Influence

**Claim.** The total influence of the real-valued form of the AND function on $n$ sign coordinates is $n/2^{n-1}$.

**Proof.** Write total influence as the sum of the coordinate influences. For each coordinate, its Boolean influence equals the influence of the real-valued form (`FABL.booleanInfluence_eq_influence_toReal`). The Boolean influence of AND is $1/2^{n-1}$ at every coordinate (`FABL.booleanInfluence_andFunction`). Summing this common value over the $n$ coordinates yields $n/2^{n-1}$.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_andFunction`.
