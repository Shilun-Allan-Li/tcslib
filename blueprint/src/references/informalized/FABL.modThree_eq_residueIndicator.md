<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThree_eq_residueIndicator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Residue indicator formula

**Claim.** The indicator of divisibility of the integer coordinate sum by $3$ equals $1$ when the sum reduced modulo $3$ is zero, and equals $0$ otherwise.

**Proof.** The mod-three indicator formula identifies the value with $1$ exactly when the integer coordinate sum is divisible by $3$, and with $0$ otherwise (\texttt{modThree_apply}). Split into the cases where the residue sum is zero or nonzero. In the zero case, the residue-divisibility criterion gives divisibility of the integer sum, so both indicator expressions equal $1$ (\texttt{modThreeResidue_eq_zero_iff}). In the nonzero case, the same criterion implies that the integer sum is not divisible by $3$, so both expressions equal $0$.

**Key facts.** `FABL.modThree_apply`, `FABL.modThreeResidue_eq_zero_iff`.
