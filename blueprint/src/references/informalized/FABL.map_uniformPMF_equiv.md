<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.map_uniformPMF_equiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Distribution Under Bijection

**Claim.** For finite nonempty sets $\alpha$ and $\beta$, mapping a uniformly chosen element of $\alpha$ through a bijection $e:\alpha\to\beta$ gives the uniform distribution on $\beta$.

**Proof.** Fix $b\in\beta$. In the probability assigned to $b$ by the image distribution, only the input $e^{-1}(b)$ contributes, since $e$ is bijective. That input has uniform probability $1/|\alpha|$. The bijection gives $|\alpha|=|\beta|$, so this equals the uniform probability $1/|\beta|$ assigned to $b$. Thus the image distribution is uniform.
