<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.isFourierSpectrumConcentratedUpTo_totalInfluenceLearningDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration at the Rounded Influence Cutoff

**Claim.** If a Boolean function has total influence at most $t$ and $\epsilon$ is a positive learning parameter, then its Fourier weight above degree $\lceil 2t/\epsilon\rceil$ is at most $\epsilon/2$.

**Proof.** The learning parameter has positive real value $\epsilon$. The total-influence concentration bound says that the Fourier weight above $\mathrm{totalInfluence}(f)/\delta$ is at most $\delta$ for every $\delta>0$; apply it with $\delta=\epsilon/2$. Since $\mathrm{totalInfluence}(f)\le t$ and $\epsilon>0$, we have $\mathrm{totalInfluence}(f)/(\epsilon/2)=2\mathrm{totalInfluence}(f)/\epsilon\le 2t/\epsilon$. The ceiling of $2t/\epsilon$ is at least $2t/\epsilon$, and raising the cutoff can only decrease the Fourier weight above it. Thus the weight above the stated integer cutoff is at most $\epsilon/2$.

**Key facts.** `FABL.positiveLearningParameter_toReal_mem_Ioc`, `FABL.isFourierSpectrumConcentratedUpTo_totalInfluence_div`, `FABL.IsFourierSpectrumConcentratedUpTo.mono_cutoff`.
