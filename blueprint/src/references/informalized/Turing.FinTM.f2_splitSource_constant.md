<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitSource_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant-Source Prefix Output

**Claim.** For every natural number $C$ and Boolean word $s$, the specified machine, started in the bank configuration on input $s$ with its initial state and empty output, halts after $C+1$ steps with output consisting of exactly $C$ copies of true.

**Proof.** First identify the bank configuration with the machine's initial configuration on empty input: both have the initial state, initial input-head position, no work tapes, and empty output. The zero-tape configuration extensionality fact (`Cfg.ext_zero_tapes`) justifies this identification. The prefix-emission result (`f2_catalogPrefixTM_emit`) then describes the configuration after $C$ steps: it has emitted the first $C$ symbols of the specified word, which here is the word of $C$ true symbols. One further transition reads the end of the empty input, enters the halted state, and leaves the output unchanged. Comparing the resulting state, input position, and output, again using zero-tape extensionality, gives the stated bank configuration.

**Key facts.** `Turing.Cfg.ext_zero_tapes`, `Turing.FinTM.f2_catalogPrefixTM_emit`.
