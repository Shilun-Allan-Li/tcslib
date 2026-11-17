<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.thirdMomentSum_rademacherSummand_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third-Moment Bound for Normalized Sums

**Claim.** If $\sum_i a_i^2=1$ and $|a_i|\le\varepsilon$ for every $i$, then the third-moment sum of the Rademacher summands $a_iX_i$ is at most $\varepsilon$.

**Proof.** The exact third-moment formula ( `thirdMomentSum_rademacherSummand`) identifies the sum with $\sum_i |a_i|^3$. Rewrite each term as $|a_i|a_i^2$, using $a_i^2=|a_i|^2$. Since $a_i^2\ge0$ and $|a_i|\le\varepsilon$, each term is at most $\varepsilon a_i^2$. Summing gives at most $\varepsilon\sum_i a_i^2=\varepsilon$.

**Key facts.** `FABL.thirdMomentSum_rademacherSummand`.
