<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathParse.lean :: Complexity.LogProg.ups_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary input initialization

**Claim.** Under the stated register bounds and pointer alignment, the program started at its initial stage has acceptance probability $q$, provided each possible unary delimiter position has the specified semantics and $q=0$ when no such delimiter exists.

**Proof.** We use strong induction on the number $dd=|x|-\sigma.p$ of input positions remaining. Since $\sigma.p=2\sigma.n$, the two bits inspected at the current pointer are exactly the pair indexed by $\sigma.n$ in the unary-input condition.

If the first bit is $0$, inspect the second bit. If it too is $0$, the program rejects. A possible delimiter cannot occur later: at its initial index the required pair would have to be $11$, contradicting the current first bit, or the delimiter would have to be the current pair, contradicting the second bit. Thus the no-delimiter hypothesis forces $q=0$, and rejection has the required semantics. If instead the pair is $01$, it is already the delimiter at $n'=\sigma.n$. The assumed semantics for that initialization state, together with the two pointer increments, gives probability $q$.

If the first bit is $1$ and the second is $0$, the program rejects. Again no valid delimiter can occur: the current pair is neither $11$ nor $01$, and any later delimiter would require the current pair to be $11$. Hence $q=0$. Finally, if the pair is $11$, advance the pointer by two and the vertex count by one. The remaining input length decreases, so the induction hypothesis applies. Every later candidate delimiter still satisfies the required unary condition: the newly passed pair supplies its first $11$ pair, and the former condition supplies all subsequent pairs and the delimiter. The no-delimiter condition also transfers, since any delimiter after the advance would have been one before it. The induction hypothesis therefore gives probability $q$ at the advanced state, and the two increments preserve that probability. The instruction-semantic facts used to lift these continuations through the program are the deterministic call and increment rules.

**Key facts.** `Complexity.LogProg.PSem.call_neg`, `Complexity.LogProg.PSem.inc`, `Complexity.LogProg.PSem.call_pos`, `Complexity.LogProg.UPS.of_eq`, `Complexity.LogProg.UReg.reg`, `Complexity.LogProg.UReg.v_0`, `Complexity.LogProg.pathOr_bit`, `Complexity.LogProg.ups_rej`, `Complexity.lt_of_getD_true`.
