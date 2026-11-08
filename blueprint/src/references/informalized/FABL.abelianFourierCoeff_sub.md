<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.abelianFourierCoeff_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficient of a Difference

**Claim.** The Fourier coefficient of $f-g$ at a character is the Fourier coefficient of $f$ minus the Fourier coefficient of $g$.

**Proof.** Express each Fourier coefficient as the uniform average of the conjugate character times the function (`FABL.complexUniformInner_eq_expect`). Distributivity gives $\overline{\chi(x)}(f(x)-g(x))=\overline{\chi(x)}f(x)-\overline{\chi(x)}g(x)$ pointwise. Linearity of the finite uniform average over differences then yields the stated identity.

**Key facts.** `FABL.complexUniformInner_eq_expect`.
