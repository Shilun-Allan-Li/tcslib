<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/InputDevice.lean :: Turing.Cfg.inputSymbol_eq_inputCell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol as an Input Cell

**Claim.** For any configuration $c$ with input word $y$, the optional symbol scanned by its input head equals the content of input cell $c$'s head position, with cell $0$ blank and the input symbols in the subsequent positions.

**Proof.** Write $p$ for the numerical input-head position. If $p=0$, both descriptions give the left boundary blank. If $p=|y|+1$, the head is beyond the last input symbol, so the scanned symbol is absent; the corresponding input-cell lookup is also absent. In the remaining case, $1\le p<|y|+1$. The head is therefore over input symbol number $p-1$. The inner-position characterization of the scanned symbol (`Turing.inputSymbolInner`) says it is that symbol, and the definition of input cells gives the same symbol at position $p$.

**Key facts.** `Turing.inputSymbolInner`.
