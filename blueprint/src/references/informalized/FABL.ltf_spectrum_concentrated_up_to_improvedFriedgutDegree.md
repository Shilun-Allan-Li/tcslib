<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.ltf_spectrum_concentrated_up_to_improvedFriedgutDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier concentration for threshold functions

**Claim.** For a Boolean linear threshold function and every $\varepsilon>0$, the Fourier weight on coordinate sets of size greater than $\lceil16/\varepsilon^2\rceil$ is at most $\varepsilon$.

**Proof.** Let $d=\lceil16/\varepsilon^2\rceil$. The ceiling property gives $16/\varepsilon^2\le d$, hence $(4/\varepsilon)^2\le d+1$. Since $\varepsilon>0$, taking nonnegative square roots yields $4/\varepsilon\le\sqrt{d+1}$, and rearranging gives $4/\sqrt{d+1}\le\varepsilon$. Apply the threshold-function tail estimate, which bounds the Fourier weight above degree $k-1$ by $4/\sqrt{k}$, with $k=d+1$. This gives a bound of $4/\sqrt{d+1}$ for the weight above degree $d$. The identification of the real degree cutoff with the natural-number cutoff then gives the claimed bound by $\varepsilon$.

**Key facts.** `FABL.fourierWeightAbove_pred_le_four_div_sqrt_of_isLinearThreshold`, `FABL.fourierWeightAboveReal_natCast`.
