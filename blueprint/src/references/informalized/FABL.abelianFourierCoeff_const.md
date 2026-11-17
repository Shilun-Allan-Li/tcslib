<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.abelianFourierCoeff_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients of Constants

**Claim.** The Fourier coefficient of the constant function with value $c$ equals $c$ at the trivial character and zero at every other character.

**Proof.** At the trivial character, the coefficient is the uniform average of the constant function, hence equals $c$. For a nontrivial character $\chi$, express the coefficient as the average of $\overline{\chi(x)}c$. The character orthogonality relation says that the uniform inner product of distinct characters is zero (`FABL.characters_orthonormal`). In particular, the average of $\overline{\chi(x)}$ is zero: it is the inner product of $\chi$ with the zero character, whose character function is constant $1$. Factoring out $c$ therefore gives coefficient zero.

**Key facts.** `FABL.complexUniformInner_eq_expect`, `FABL.characters_orthonormal`.
