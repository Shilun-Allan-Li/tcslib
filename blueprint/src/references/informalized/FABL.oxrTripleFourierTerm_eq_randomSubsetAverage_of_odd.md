<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oxrTripleFourierTerm_eq_randomSubsetAverage_of_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Fourier term as a subset average

**Claim.** For an odd function, the stated weighted sum over subsets, multiplied by $\widehat f(S)^2$, equals $\widehat f(S)^2$ times the signed random-subset average of the Fourier coefficient at $S\cap K$.

**Proof.** Split according to the parity of $|S|$. If $|S|$ is even, oddness forces $\widehat f(S)=0$ (`FABL.fourierCoeff_even_eq_zero_of_odd`), so both sides vanish. Suppose instead that $|S|$ is odd. It remains to identify the two expressions inside the common factor $\widehat f(S)^2$. The intersection-average formula rewrites the random-subset average as a sum over $J\subseteq S$, whose weight is $(1-\delta)^{|J|}\delta^{|S|-|J|}$, multiplied by $(-1)^{|J|}\widehat f(J)$ (`FABL.expectDeltaRandomSubset_intersection_eq_sum`). For an even-sized $J$, the Fourier coefficient vanishes by oddness. For an odd-sized $J$, both $|J|$ and $|S|-|J|$ are odd. Consequently, extracting the signs from $(-(1-\delta))^{|J|}$ and $(-\delta)^{|S|-|J|}$ gives a net positive sign, equal to the sign from the factor $(-1)^{|J|}$ in the random-subset average. The summands therefore agree for every $J\subseteq S$, and the sums agree. Multiplying by $\widehat f(S)^2$ proves the identity.

**Key facts.** `FABL.fourierCoeff_even_eq_zero_of_odd`, `FABL.expectDeltaRandomSubset_intersection_eq_sum`.
