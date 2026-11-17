<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.spectrum_concentrated_on_empty_of_totalInfluence_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero influence concentrates the spectrum

**Claim.** If a Boolean function has total influence zero, then its Fourier spectrum is concentrated outside the subsets of the empty set with weight zero; in particular, the required concentration bound holds for every nonnegative $\epsilon$.

**Proof.** The spectrum outside the family of subsets of the empty set is the sum of the Fourier weights indexed by nonempty sets. For each such set $S$, the zero-total-influence hypothesis forces $\widehat f(S)=0$ (`fourierCoeff_eq_zero_of_totalInfluence_eq_zero`). Hence every summand, being the square of that coefficient, vanishes, and the entire finite sum is zero. Since $0\leq\epsilon$, this sum is at most $\epsilon$, which is precisely the stated concentration condition.

**Key facts.** `FABL.fourierCoeff_eq_zero_of_totalInfluence_eq_zero`.
