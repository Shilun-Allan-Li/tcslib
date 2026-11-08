<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/MaioranaMcFarlandPermutation.lean :: FABL.isSignValued_maioranaMcFarlandPermutation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permuted Maiorana–McFarland Is Sign-Valued

**Claim.** For every permutation and sign-valued function $g$, the permuted Maiorana–McFarland function has absolute value $1$ at every input.

**Proof.** Fix an input and split it into blocks $x$ and $y$. On their concatenation, the function is the product of the binary sign of $x\cdot\pi(y)$ and the real value of $g(y)$ (\(\texttt{maioranaMcFarlandPermutation\_joinF₂CubeBlocks}\)). The first factor is a Walsh character value by its evaluation formula (\(\texttt{vectorWalshCharacter\_apply}\)), hence has absolute value $1$ (\(\texttt{abs\_vectorWalshCharacter}\)). The second factor is either $-1$ or $1$ (\(\texttt{signValue\_eq\_neg\_one\_or\_one}\)), so its absolute value is also $1$. The product therefore has absolute value $1$.

**Key facts.** `FABL.maioranaMcFarlandPermutation_joinF₂CubeBlocks`, `FABL.vectorWalshCharacter_apply`, `FABL.abs_vectorWalshCharacter`, `FABL.signValue_eq_neg_one_or_one`.
