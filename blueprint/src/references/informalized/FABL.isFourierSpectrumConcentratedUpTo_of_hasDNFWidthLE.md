<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.isFourierSpectrumConcentratedUpTo_of_hasDNFWidthLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Concentration for Bounded-Width DNF

**Claim.** If a Boolean function has a DNF representation of width at most $w$, then its Fourier spectrum is $\epsilon$-concentrated through degree $2w/\epsilon$ for every positive $\epsilon$.

**Proof.** A DNF of width at most $w$ has total influence at most $2w$. The general total-influence concentration bound gives concentration through degree $\operatorname{Inf}(f)/\epsilon$. Since $\epsilon>0$, replacing the numerator by the upper bound $2w$ can only increase this cutoff. Concentration is preserved when the cutoff is increased, yielding the stated degree bound.

**Key facts.** `FABL.totalInfluence_le_two_mul_of_hasDNFWidthLE`, `FABL.isFourierSpectrumConcentratedUpTo_totalInfluence_div`, `FABL.IsFourierSpectrumConcentratedUpTo.mono_cutoff`.
