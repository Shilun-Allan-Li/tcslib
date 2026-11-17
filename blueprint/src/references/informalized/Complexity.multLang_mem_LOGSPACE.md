<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.multLang_mem_LOGSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplication in Log Space

**Claim.** The language of encodings of triples consisting of two nonnegative integers and their product is decidable in logarithmic space.

**Proof.** Apply the general logarithmic-space theorem for alternating register machines with log-space oracle languages (`Complexity.LogProg.arm_decides_poly`) to the multiplication machine. Its two oracle languages, which test the input bits and input length, are both in log space (`Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`). The machine's correctness condition is supplied by the multiplication run result (`Complexity.mult_run`): on each input, it halts with the indicator of membership in the multiplication language. The indicator is identified with the usual decision test (`Complexity.LogProg.indicator_eq_decide`), so the general theorem yields the claimed log-space membership.

**Key facts.** `Complexity.LogProg.arm_decides_poly`, `Complexity.inputBitLang_mem`, `Complexity.inputLenLang_mem`, `Complexity.mult_run`, `Complexity.LogProg.indicator_eq_decide`.
