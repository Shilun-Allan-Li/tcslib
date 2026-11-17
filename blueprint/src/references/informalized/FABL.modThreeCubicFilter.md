<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeCubicFilter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cubic Character Filter Identity

**Claim.** For every $a\in\mathbb Z/3\mathbb Z$, the indicator of $a=0$ equals $\frac13+\frac23\operatorname{Re}(\chi(a))$.

**Proof.** There are three residues, so check them individually. At $a=0$, the character value is $1$, and the right side is $1/3+2/3=1$, matching the indicator. At $a=1$, the character value is $\zeta=-1/2+(\sqrt3/2)i$, whose real part is $-1/2$; the right side is therefore zero. At $a=2$, the character value is $\zeta^2=-1/2-(\sqrt3/2)i$, again with real part $-1/2$, so the right side is zero. These are precisely the indicator values at the three residues.

**Key facts.** `FABL.modThreeCubicCharacter_zero`, `FABL.modThreeCubicCharacter_one`, `FABL.modThreeCubicRoot_eq`, `FABL.modThreeCubicCharacter_two`, `FABL.modThreeCubicRoot_sq`.
