<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.totalInfluence_gotsmanLinialExtremizer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of the Gotsman–Linial Extremizer

**Claim.** For all natural numbers $n,k$, the total influence of the specified Gotsman–Linial extremizer equals $\frac{n}{2^{n-1}}$ times the sum of the indicated binomial coefficients.

**Proof.** If $n=0$, the total influence and the stated expression both vanish. Otherwise write $n=m+1$. For each coordinate, its Boolean influence equals the real-valued influence (`FABL.booleanInfluence_eq_influence_toReal`), and the extremizer's coordinate influence is the same sum of binomial coefficients divided by $2^m$ (`FABL.booleanInfluence_gotsmanLinialExtremizer`). Summing this identical quantity over the $m+1=n$ coordinates multiplies it by $n$. Since $2^m=2^{n-1}$, this gives the asserted formula.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_gotsmanLinialExtremizer`.
