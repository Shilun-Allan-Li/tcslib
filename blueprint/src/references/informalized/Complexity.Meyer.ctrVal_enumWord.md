<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.ctrVal_enumWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of a Fixed-Width Binary Word

**Claim.** For natural numbers $w,v$ with $v<2^w$, the binary value of the width-$w$ little-endian binary word of $v$ is $v$.

**Proof.** Induct on the width $w$, generalizing over $v$. At width zero the bound forces $v=0$, and both the empty word's value and $v$ are zero. At width $w+1$, the word begins with the parity bit of $v$, followed by the width-$w$ word for $v/2$. The bound implies $v/2<2^w$, so the induction hypothesis evaluates the tail as $v/2$. Since the remainder of division by two is either zero or one, the defining value formula gives the parity bit plus $2(v/2)$, which equals $v$.
