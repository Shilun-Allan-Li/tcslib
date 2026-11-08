<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.tendsto_normalizedGotsmanLinialTotalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic normalized total influence

**Claim.** For each fixed \(k\ge0\), the normalized total influence of the degree-\(k\) Gotsman–Linial extremizer tends to \(k\sqrt{2/\pi}\) as the dimension parameter tends to infinity.

**Proof.** Split into the cases \(k=0\) and \(k>0\). If \(k=0\), the exact total-influence formula for the extremizer shows that its total influence is zero in every dimension (\(\texttt{totalInfluence\_gotsmanLinialExtremizer}\)). The normalized sequence is therefore constantly zero, giving the asserted limit. If \(k>0\), the even and odd subsequences both tend to \(k\sqrt{2/\pi}\), by the corresponding subsequence limit theorems. A sequence whose even and odd subsequences converge to the same value converges to that value (\(\texttt{tendsto\_nat\_of\_even\_odd}\)).

**Key facts.** `FABL.totalInfluence_gotsmanLinialExtremizer`, `FABL.tendsto_normalizedGotsmanLinialTotalInfluence_even`, `FABL.tendsto_normalizedGotsmanLinialTotalInfluence_odd`, `FABL.tendsto_nat_of_even_odd`.
