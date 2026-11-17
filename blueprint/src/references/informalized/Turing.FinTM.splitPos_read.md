<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitPos_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading at a Saturated Position

**Claim.** Let $w$ be a Boolean word and let $c$ be a configuration on input $w$. If its input head is at the saturated position $\min(j,|w|)+1$, then it reads the $j$-th bit of $w$ when $j<|w|$, and reads no symbol when $j\ge |w|$.

**Proof.** Split into the two possibilities for $j$. If $j<|w|$, then $\min(j,|w|)=j$, so the head position is $j+1$. The fact that a head at position $p+1$ reads the $p$-th input symbol, provided $p<|w|$, gives the result ($\texttt{Turing.inputSymbolInner}$). If $j\ge |w|$, then $\min(j,|w|)=|w|$, so the head is at position $|w|+1$, the right boundary position. By the definition of the input-symbol reading function, that position reads no symbol.

**Key facts.** `Turing.inputSymbolInner`.
