<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.goes_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal-table prefix execution

**Claim.** For the input consisting of $n$ ones, a zero, $T$ ones, a second zero, and then $z$, the counter program reaches the layout phase with the stated input position, registers, and output, using at most the stated prefix bound.

**Proof.** Write $w$ for the specified input. The proof concatenates the program’s successive phases. First, the unary input scan reads the initial $n$ ones, increases the input-count register by $n$, and prints those ones; this takes at most $3n$ steps (the unary scan result `goes_rN`). Reading the first zero advances the input position by one, and the following output instruction prints that zero. The budget scan then reads the next $T$ ones, placing $T$ in the step-budget register in at most $2T$ steps (`goes_rT`). Reading the second zero advances the position once more.

Next, the preamble template emits the encodings of the false and true constant gates, in at most $L+1$ steps (`goes_tp` and the template-length bound `length_tmpl_le`). The hard-wired-input scan processes each bit of $z$: for each bit it emits that bit’s constant-gate encoding and increments the hard-wired-length register. Thus this phase consumes $|z|$ input symbols, emits the encodings of the successive bits, and takes at most $|z|(L+3)$ steps (`goes_rZ`). At the end of $z$, the input position is $n+T+|z|+2$. The next read detects the end of the input without changing the position (`goes_rd_end`). Finally, the dummy template emits $W$ false constant gates and proceeds to the layout label; this costs at most $L+1$ steps.

The register records at the phase boundaries show that the input-count, hard-wired-length, and budget registers contain $n$, $|z|$, and $T$, respectively, while the other registers remain zero. Concatenating the phase runs adds their step bounds and concatenates their outputs (`Goes.trans`); identifying the resulting output with the stated prefix and bounding the sum by the displayed expression completes the argument.

**Key facts.** `Complexity.UTab.goes_rN`, `Complexity.CounterProg.goes_rd_false`, `Complexity.CounterProg.goes_out`, `Complexity.UTab.goes_rT`, `Complexity.UTab.goes_tp`, `Complexity.UTab.goes_rZ`, `Complexity.CounterProg.goes_rd_end`, `Complexity.UTab.length_tmpl_le`, `Complexity.CounterProg.Goes.trans`.
