<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterToken_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Token Encoder Run

**Claim.** If $x=pr$, then starting just after $p$ in the token-scanning state with output $o$, the encoder halts after $2|a|+|b|+3$ steps with output $o$ followed by the self-delimiting encoding of the token and remainder $(a,b)$ obtained by splitting $r$.

**Proof.** Induct on the suffix $r$. If $r$ is empty, the machine reads the end of the input, emits the two-bit separator $0,1$, and then halts; these are the three steps in the stated bound. The result is precisely the encoding of the empty token and empty remainder. For a nonempty suffix, write it as $b::r'$. The two-step token transition emits $bb$ and advances to just after this bit (`Turing.FinTM.emitterToken_double`). If $b$ is false, this transition enters the separator phase: the machine emits $0,1$, then copies the remaining suffix and halts (`Turing.FinTM.emitterToken_separator` and `Turing.FinTM.scanCopy_suffix`). The resulting output is the encoding of the one-bit false token and that suffix. If $b$ is true, the machine returns to the token-scanning state just after the true bit. Apply the induction hypothesis to $r'$ with this longer prefix and the output extended by $11$. In either case, the two initial steps plus the remaining run give the stated time; associativity of concatenation identifies the resulting output with the pair encoding.

**Key facts.** `Turing.FinTM.emitterToken_double`, `Turing.FinTM.emitterToken_separator`, `Turing.FinTM.scanCopy_suffix`, `Turing.MultiTapeTM.runFrom_add`.
