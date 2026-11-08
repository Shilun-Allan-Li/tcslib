<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.scanCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol in a Scan Configuration

**Claim.** In the specified scan configuration at position $i+1$, the input symbol is the optional list entry $x[i]?$.

**Proof.** If $i<|x|$, the optional list entry $x[i]?$ is the actual element $x[i]$, and the input-head position is $1+i$. The input-reading fact (`inputSymbolInner`) therefore gives the same symbol. If $i$ is not less than the input length, the hypothesis $i\le |x|$ forces $i=|x|$. The head is then at the blank just beyond the input, so the scanned symbol and the optional list entry are both none.

**Key facts.** `Turing.inputSymbolInner`.
