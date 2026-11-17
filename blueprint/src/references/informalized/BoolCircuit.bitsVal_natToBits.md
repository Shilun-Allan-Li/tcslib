<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/AdderLanguage.lean :: BoolCircuit.bitsVal_natToBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the Low-Order Bits

**Claim.** If $m<2^k$, then the length-$k$ list of the binary digits of $m$ has base-two value $m$.

**Proof.** Induct on $k$, allowing $m$ to vary. When $k=0$, the bound forces $m=0$, and the empty list has value zero. For the successor step, the list of the first $k+1$ bits consists of the lowest bit of $m$, followed by the first $k$ bits of $\floor{m/2}$. The bound $m<2^{k+1}$ implies $\floor{m/2}<2^k$, so the induction hypothesis gives value $\floor{m/2}$ for that tail. The base-two value of the whole list is therefore the lowest bit plus twice $\floor{m/2}$. The usual quotient-and-remainder decomposition of $m$ by $2$ says exactly that this is $m$.
