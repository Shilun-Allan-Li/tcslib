<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol at an Interior Position

**Claim.** When the threaded-map configuration has input-head position $i+1$, it reads the $i$-th input bit, or no symbol when $i$ is the input length.

**Proof.** Apply the general input-symbol-at-position fact to the threaded-map configuration. Its input-head position has value $i+1$ by construction, and the assumed bound $i\le |x|$ supplies the required index bound. The result is exactly that the scanned symbol is $x[i]?$.

**Key facts.** `Turing.FinTM.inputSymbol_at`.
