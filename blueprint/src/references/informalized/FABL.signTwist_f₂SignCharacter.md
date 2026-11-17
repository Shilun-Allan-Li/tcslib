<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.signTwist_f₂SignCharacter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product of binary sign characters

**Claim.** For any $a,\gamma\in(\mathbb F_2)^n$, multiplying the sign character associated with $\gamma$ pointwise by the one associated with $a$ gives the character associated with $\gamma+a$.

**Proof.** Fix $z\in(\mathbb F_2)^n$. The two character values at $z$ are the signs encoded by $\langle\gamma,z\rangle$ and $\langle a,z\rangle$. The product of signs encoded by two elements of $\mathbb F_2$ is the sign encoded by their sum ($\mathrm{signEncode\_add}$). Bilinearity of the dot product gives $\langle\gamma,z\rangle+\langle a,z\rangle=\langle\gamma+a,z\rangle$. Thus the two sides agree at every $z$, proving equality of the functions.

**Key facts.** `FABL.signEncode_add`.
