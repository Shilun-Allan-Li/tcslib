<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalPrefix_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Parser Halting Configuration

**Claim.** After $2|\alpha|+2$ steps, the prefix parser is halted, its input head is at position $2|\alpha|+3$, and its output is $\alpha$.

**Proof.** Use the even-time description at $j=|\alpha|$ to reach the ready-to-read state after $2|\alpha|$ steps, with output $\alpha$ (`universalPrefix_bits`). The next step reads the first separator bit, which is $0$ (`universal_pair_separator` and `inputSymbol_at`). This records the separator and moves the head right without changing the output, giving the penultimate configuration. The final step reads the second separator bit, which is $1$. The parser’s transition on this bit halts and emits nothing; the head moves right once more. The head-movement formula gives position $2|\alpha|+3$ (`moveInputPos_pos_of_ne_right`), and extensionality for configurations with no work tapes confirms that the state, position, and output are precisely those asserted (`Cfg.ext_zero_tapes`).

**Key facts.** `Turing.universal_pair_length`, `Turing.universal_pair_separator`, `Turing.universalPrefix_bits`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.inputSymbol_at`, `Turing.universalPrefix_step`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.Cfg.ext_zero_tapes`.
