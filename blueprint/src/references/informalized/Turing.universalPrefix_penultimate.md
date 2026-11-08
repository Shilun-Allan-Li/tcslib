<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalPrefix_penultimate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Parser Before Halting

**Claim.** After $2|\alpha|+1$ steps, the prefix parser is live, records the bit $0$, has its input head at position $2|\alpha|+2$, and has output exactly $\alpha$.

**Proof.** Apply the even-time prefix description with $j=|\alpha|$: after $2|\alpha|$ steps the parser is ready for a pair, its head is at $2|\alpha|+1$, and its output is $\alpha$ (`universalPrefix_bits` and the identity $\alpha.take|\alpha|=\alpha$). One more step reads the first separator bit. The separator fact identifies it as $0$ (`universal_pair_separator`), and the input-symbol lemma makes this the symbol scanned by the parser (`inputSymbol_at`). The parser’s transition on that bit records $0$, emits nothing, and moves right. The rightward head-movement formula gives position $2|\alpha|+2$ (`moveInputPos_pos_of_ne_right`). Thus the state is live with the recorded bit, while the output remains $\alpha$.

**Key facts.** `Turing.universal_pair_length`, `Turing.universalPrefix_bits`, `Turing.universal_pair_separator`, `Turing.FinTM.inputSymbol_at`, `Turing.universalPrefix_step`, `Turing.moveInputPos_pos_of_ne_right`.
