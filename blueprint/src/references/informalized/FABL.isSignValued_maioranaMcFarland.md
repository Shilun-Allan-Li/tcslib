<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.isSignValued_maioranaMcFarland -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maiorana–McFarland Is Sign-Valued

**Claim.** For every sign-valued function $g$, the Maiorana–McFarland function has absolute value $1$ at every input.

**Proof.** Fix an input and write it as the concatenation of blocks $x$ and $y$. On such an input, the function is the product of the binary sign of $x\cdot y$ and the real value of $g(y)$ (\(\texttt{maioranaMcFarland\_joinF₂CubeBlocks}\)). The first factor has absolute value $1$: by the character evaluation formula (\(\texttt{vectorWalshCharacter\_apply}\)), it is a Walsh character value, whose absolute value is $1$ (\(\texttt{abs\_vectorWalshCharacter}\)). The second factor is either $-1$ or $1$ (\(\texttt{signValue\_eq\_neg\_one\_or\_one}\)), so it too has absolute value $1$. Multiplicativity of absolute value gives the claim.

**Key facts.** `FABL.maioranaMcFarland_joinF₂CubeBlocks`, `FABL.vectorWalshCharacter_apply`, `FABL.abs_vectorWalshCharacter`, `FABL.signValue_eq_neg_one_or_one`.
