<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeReadOutput_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optional Output Reader Soundness

**Claim.** If the optional-output reader succeeds on $x$ with result $(b,r)$, then $x$ is the two-bit code for $b$ followed by $r$.

**Proof.** Inspect the input by its length and first two bits. An empty input or a one-bit input cannot match any successful reader clause. With at least two bits, the reader succeeds only on $00$, $10$, or $11$: these yield, respectively, no output, output $0$, or output $1$, with the remaining tail as $r$. In each successful case, the input is exactly the corresponding two-bit code for $b$ followed by $r$.
