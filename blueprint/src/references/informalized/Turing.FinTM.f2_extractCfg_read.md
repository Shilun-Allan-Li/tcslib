<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_extractCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol in an Extractor Configuration

**Claim.** For the stated extractor configuration with input head at position $i+1$, the scanned input symbol is $x[i]?$—the $i$th symbol when it exists, and no symbol when $i=|x|$.

**Proof.** The extractor configuration has the same input word, head position, and output as the scan configuration in the scan-read lemma; its tape contents and state do not affect the input symbol. Applying that lemma ($\texttt{Turing.FinTM.f2_scanCfg_read}$) gives exactly $x[i]?$.

**Key facts.** `Turing.FinTM.f2_scanCfg_read`.
