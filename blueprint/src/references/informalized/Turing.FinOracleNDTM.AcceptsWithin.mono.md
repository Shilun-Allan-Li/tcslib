<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.FinOracleNDTM.AcceptsWithin.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of bounded acceptance

**Claim.** If a choice sequence of length $t$ makes the oracle machine halt with output $[\mathrm{true}]$, then for every $t'\geq t$ there is a choice sequence of length $t'$ with the same accepting outcome.

**Proof.** Take a witnessing sequence $w$ of length $t$ and append $t'-t$ arbitrary choice bits. The resulting word has length $t'$. By the run-on-concatenation law (`runWith_append`), its run continues from the run on $w$. Since that run has halted, further choices leave the configuration unchanged (`runWith_of_halt`); it therefore still halts and still has output $[\mathrm{true}]$.

**Key facts.** `Turing.OracleNDTM.runWith_append`, `Turing.OracleNDTM.runWith_of_halt`.
