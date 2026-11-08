<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.continuousOn_gaussianIsoperimetricReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Extended Gaussian Isoperimetric Profile

**Claim.** The continuous extension of the interior Gaussian isoperimetric profile to $[0,1]$, with endpoint values zero, is continuous on $[0,1]$.

**Proof.** The interior profile is continuous on $(0,1)$ (continuousOn_gaussianIsoperimetricInterior). As the argument approaches $0$ from within the interval, the profile tends to $0$ (tendsto_gaussianIsoperimetricInterior_zero); as it approaches $1$ from within, it also tends to $0$ (tendsto_gaussianIsoperimetricInterior_one). The extension theorem for a function continuous on $(0,1)$ with these one-sided endpoint limits gives continuity of its extension on $[0,1]$ (continuousOn_Icc_extendFrom_Ioo). The extension used here is the stated Gaussian isoperimetric profile.

**Key facts.** `FABL.continuousOn_gaussianIsoperimetricInterior`, `FABL.tendsto_gaussianIsoperimetricInterior_zero`, `FABL.tendsto_gaussianIsoperimetricInterior_one`.
