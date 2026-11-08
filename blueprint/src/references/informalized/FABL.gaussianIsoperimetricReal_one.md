<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetricConcavity.lean :: FABL.gaussianIsoperimetricReal_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Isoperimetric Function at One

**Claim.** The real-valued Gaussian isoperimetric function satisfies $I(1)=0$.

**Proof.** The real-valued function is defined by extending its interior profile from $(0,1)$. Its value at the right endpoint equals the limit of that interior profile as the argument approaches $1$ from below. The interior profile tends to $0$ there (\texttt{FABL.tendsto\_gaussianIsoperimetricInterior\_one}), so the endpoint value is $0$.

**Key facts.** `FABL.tendsto_gaussianIsoperimetricInterior_one`.
