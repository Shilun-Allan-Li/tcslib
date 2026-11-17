<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_lenCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol at a Prescribed Position

**Claim.** The input symbol scanned by the length-counting configuration at position $i+1$ is $x[i]?$, including the empty value when $i$ is at or beyond the end of $x$.

**Proof.** The input-symbol formula for a configuration whose head position has value $i+1$ returns the symbol of the input at index $(i+1)-1=i$, with out-of-range indices represented by `none`. The length-counting configuration has exactly that head position, so its scanned symbol is $x[i]?$. This is precisely the fact that a head at the shifted position $i+1$ reads the $i$-th input symbol, or no symbol when that index is out of range (`inputSymbol_at`).

**Key facts.** `Turing.FinTM.inputSymbol_at`.
