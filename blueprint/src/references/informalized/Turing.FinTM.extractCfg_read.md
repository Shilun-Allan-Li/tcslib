<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.extractCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the input symbol in an extractor configuration

**Claim.** The extractor configuration positioned just past the first $i$ symbols reads $x[i]?$; in particular, it reads the next input bit when $i<|x|$ and no symbol when $i=|x|$.

**Proof.** The extractor configuration has input-head position $i+1$ in the shifted indexing convention. The scan-configuration reading lemma (`Turing.FinTM.scanCfg_read`) states that a configuration with this position reads exactly the list entry $x[i]?$. The extractor differs only in its buffered work tape and output, which do not affect the input symbol, so the lemma applies directly.

**Key facts.** `Turing.FinTM.scanCfg_read`.
