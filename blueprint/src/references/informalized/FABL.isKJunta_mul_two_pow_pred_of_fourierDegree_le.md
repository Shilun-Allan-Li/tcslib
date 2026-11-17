<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.isKJunta_mul_two_pow_pred_of_fourierDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Degree Bounds Junta Size

**Claim.** A Boolean function of Fourier degree at most $k$ is a $k2^{k-1}$-junta.

**Proof.** If $k=0$, the zero-degree junta result gives the claim directly (\(\texttt{FABL.isKJunta\_zero\_of\_fourierDegree\_eq\_zero}\)). Suppose then that $k>0$. For any relevant coordinate, its influence is positive. The Boolean influence bound says that its influence is either zero or at least $2(1/2)^k$ when the Fourier degree is at most $k$ (\(\texttt{FABL.booleanInfluence\_eq\_zero\_or\_two\_mul\_inv\_two\_pow\_le}\)). Boolean influence equals the influence of the real-valued sign representation (\(\texttt{FABL.booleanInfluence\_eq\_influence\_toReal}\)), so the zero alternative is impossible for a relevant coordinate. Each relevant coordinate therefore has influence at least $2(1/2)^k=1/2^{k-1}$. Summing over relevant coordinates bounds their number divided by $2^{k-1}$ by total influence (\(\texttt{FABL.mul\_card\_relevantCoordinates\_le\_totalInfluence}\)). Total influence of a Boolean function is at most its Fourier degree, hence at most $k$ (\(\texttt{FABL.totalInfluence\_toReal\_le\_fourierDegree}\)). It follows that the number of relevant coordinates is at most $k2^{k-1}$. A Boolean function with at most that many relevant coordinates is a junta of that size (\(\texttt{FABL.isKJunta\_of\_card\_relevantCoordinates\_toReal\_le}\)), as required.

**Key facts.** `FABL.isKJunta_zero_of_fourierDegree_eq_zero`, `FABL.booleanInfluence_eq_zero_or_two_mul_inv_two_pow_le`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.mul_card_relevantCoordinates_le_totalInfluence`, `FABL.totalInfluence_toReal_le_fourierDegree`, `FABL.isKJunta_of_card_relevantCoordinates_toReal_le`.
