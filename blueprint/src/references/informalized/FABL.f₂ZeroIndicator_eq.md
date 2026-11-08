<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.f₂ZeroIndicator_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary zero indicator

**Claim.** For every $b\in\mathbb F_2$, the indicator of $b=0$ equals $(1+\chi(b))/2$, where $\chi$ is the binary sign character.

**Proof.** Split into the two cases. If $b=0$, the character takes value $1$, so both sides equal $1$. If $b\ne0$, the only other element of $\mathbb F_2$ is $1$; the character takes value $-1$ there, so both sides equal $0$.
