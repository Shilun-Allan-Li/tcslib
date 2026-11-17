<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.gaussianIsoperimetricReal_eq_gaussianIsoperimetric -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Gaussian Isoperimetric Profiles

**Claim.** For every $\alpha\in[0,1]$, the Gaussian isoperimetric profile on the unit interval equals the profile defined on the real line at $\alpha$.

**Proof.** Every point of the unit interval is either an endpoint or lies in $(0,1)$. At $0$ and $1$, both definitions give zero, so the profiles agree there. For an interior point, the real-line profile is given by its interior density formula (\texttt{FABL.gaussianIsoperimetricReal\_apply\_of\_mem\_Ioo}), and the unit-interval profile has the same formula (\texttt{FABL.gaussianIsoperimetric\_apply\_of\_mem\_Ioo}). Thus they agree in all cases.

**Key facts.** `FABL.gaussianIsoperimetricReal_apply_of_mem_Ioo`, `FABL.gaussianIsoperimetric_apply_of_mem_Ioo`.
