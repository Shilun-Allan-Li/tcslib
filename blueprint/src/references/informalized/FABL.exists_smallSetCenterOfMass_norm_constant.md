<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SmallSetCenterOfMass.lean :: FABL.exists_smallSetCenterOfMass_norm_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Center of Mass Norm Bound

**Claim.** Under the stated assumptions on $f$ and $\alpha$, the center of mass has norm at most a constant times $\sqrt{\log_2(1/\alpha)}$.

**Proof.** Take the positive constant $C$ supplied by the squared-norm estimate, and set $D=\sqrt C$. The squared-norm estimate bounds the sum of the squares of the center-of-mass coordinates by $C\log_2(1/\alpha)$. The Euclidean norm squared is exactly this sum: this follows from the $L^2$ norm formula, with absolute values disappearing after squaring. Taking square roots preserves the inequality, since both sides are nonnegative. Finally, $\sqrt{C\log_2(1/\alpha)}=D\sqrt{\log_2(1/\alpha)}$, as $C>0$.

**Key facts.** `FABL.exists_smallSetCenterOfMass_sqNorm_constant`.
