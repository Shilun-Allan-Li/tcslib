<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDiag_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of the Pairing Machine

**Claim.** Let $x$ be a bit string, $q$ one of the six control states, $p$ an input-head position, $w$ an output string, and $b$ either a bit or no symbol. If the configuration in state $q$, at position $p$, with output $w$ scans $b$, then one machine step yields the configuration whose state, input-head position, and output are prescribed by the transition table for state $q$ and scanned symbol $b$: the head moves according to the prescribed direction, with boundary clamping, and the emitted symbol, if any, is appended to $w$.

**Proof.** Because the configuration is in a nonhalting state, one machine step applies the transition table to its scanned input symbol and its work-tape symbols. There are no work tapes here, and the hypothesis identifies the scanned symbol as $b$. Thus the resulting state and input-head movement are exactly those specified by the transition for $(q,b)$, while the output is $w$ with the optional emitted symbol appended. The two configurations have zero work tapes, so their equality follows by checking state, head position, and output (`Turing.Cfg.ext_zero_tapes`).

**Key facts.** `Turing.Cfg.ext_zero_tapes`.
