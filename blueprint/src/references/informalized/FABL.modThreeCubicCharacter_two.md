<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeCubicCharacter_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character Value at Residue Two

**Claim.** For the additive character $\chi$ of $\mathbb Z/3\mathbb Z$ determined by $\chi(1)=\zeta$, its value at $2$ is $\chi(2)=\zeta^2$.

**Proof.** By the defining formula for the character `AddChar.zmodChar`, its value at a residue is the corresponding power of the chosen cubic root. The residue of $2$ has representative $2$ in the range from $0$ to $2$, so evaluating the character gives $\chi(2)=\zeta^2$.
