<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_scanCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol in a Scan Configuration

**Claim.** For a Boolean word $x$, a state option $q$, an output word, and $i\le |x|$, the input symbol in the scan configuration at position $i+1$ is $x[i]?$.

**Proof.** Split into the cases $i<|x|$ and $i\not<|x|$. In the first case, $x[i]?=some\ x[i]$. The scan configuration has input position $i+1$, so the input-symbol-at-an-interior-position fact (`Turing.inputSymbolInner`) says that its input symbol is exactly $some\ x[i]$. In the remaining case, the bound $i\le|x|$ forces $i=|x|$. The scan configuration is then at the right boundary, where the input-symbol definition returns no symbol; this equals the out-of-range option $x[|x|]?$.

**Key facts.** `Turing.inputSymbolInner`.
