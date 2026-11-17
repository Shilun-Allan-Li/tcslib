<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.characterConj_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjugation of a Character

**Claim.** For a character $\chi$ of a finite additive commutative group and any $x$ in the group, its conjugate character evaluated at $x$ equals the complex conjugate of $\chi(x)$.

**Proof.** The conjugate character is defined as the inverse of $\chi$. Evaluation of the inverse character at $x$ is the inverse of $\chi(x)$. Character values lie on the complex unit circle, so their multiplicative inverse equals their complex conjugate. Thus the value is $\overline{\chi(x)}$.
