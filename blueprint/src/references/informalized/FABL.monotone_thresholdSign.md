<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.monotone_thresholdSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Threshold Sign

**Claim.** The map sending a real number $t$ to $1$ when $t\geq0$ and to $-1$ when $t<0$ is monotone.

**Proof.** Take $a\le b$. If $a\ge0$, then also $b\ge0$, so both threshold signs are $1$. If $a<0$ and $b\ge0$, their threshold signs are $-1$ and $1$, in increasing order. If both are negative, both threshold signs are $-1$. These cases establish monotonicity.
