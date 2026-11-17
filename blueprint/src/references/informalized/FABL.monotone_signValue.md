<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.monotone_signValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Sign Value

**Claim.** The map sending each sign $s\in\{-1,1\}$ to its real value is monotone.

**Proof.** Let $a\le b$ be signs. Each is either $-1$ or $1$, so there are four cases. When they agree, their real values agree. The case $a=1$ and $b=-1$ contradicts $a\le b$, since $1\nleq -1$. The only remaining unequal case is $a=-1$, $b=1$, whose real values are ordered as claimed.
