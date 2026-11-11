<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumWord_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of an In-Range Binary Word

**Claim.** For natural numbers $w$ and $i$ with $i<2^w$, the little-endian value of the width-$w$ binary word of $i$ is $i$.

**Proof.** Induct on $w$, with $i$ arbitrary. If $w=0$, the hypothesis $i<1$ forces $i=0$, and the width-zero word is empty, of value zero. For the step, write the width-$(w+1)$ word as its first bit, determined by whether $i$ is odd, followed by the width-$w$ word of $
u=\floor{i/2}$. From $i<2^{w+1}$ it follows that $
u<2^w$, so induction gives value $
u$ for the remaining word. The value of the whole word is therefore $2
u$ plus $1$ exactly when $i$ is odd. Euclidean division by $2$ says this is $i$, proving the claim.
