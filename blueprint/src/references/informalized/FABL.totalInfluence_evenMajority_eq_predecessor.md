<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/EvenMajority.lean :: FABL.totalInfluence_evenMajority_eq_predecessor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Dimension and Its Predecessor

**Claim.** For positive even $n$, every majority function on the $n$-dimensional cube has the same total influence as majority on the $(n-1)$-dimensional cube.

**Proof.** Write the positive even integer as $n=2k$. Positivity implies $k>0$, so write $k=m+1$. Then $n=2m+2$ and $n-1=2m+1$. The even-to-odd majority influence equality (`FABL.totalInfluence_evenMajority_eq_oddMajority`) now gives precisely the desired identity.

**Key facts.** `FABL.totalInfluence_evenMajority_eq_oddMajority`.
