<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.characterMulConj_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product with a Conjugate Character

**Claim.** For additive characters $\phi$ and $\chi$ and any group element $x$, the character formed from $\phi$ and the conjugate character associated with $\chi$ takes the value $\phi(x)\overline{\chi(x)}$.

**Proof.** Evaluation of a product of characters is the product of their values. The conjugate character associated with $\chi$, evaluated at $x$, is $\overline{\chi(x)}$ by the conjugation formula (\texttt{FABL.characterConj_apply}). Multiplying by $\phi(x)$ gives the claimed expression.

**Key facts.** `FABL.characterConj_apply`.
