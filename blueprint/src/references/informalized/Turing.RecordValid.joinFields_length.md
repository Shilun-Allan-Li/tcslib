<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.RecordValid.joinFields_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Valid Configuration Record

**Claim.** If $fs$ is a valid record for a configuration with $k$ work tapes, input length $n$, and window bound $s$, joining its fields with separators gives a list of length $k(2s+1)+\mathrm{posWidth}(n)+k+4$.

**Proof.** By validity, choose an input $x$, configuration $c$, and tag witnessing that $fs$ is the corresponding configuration record, with $x$ of length $n$. The length formula for joining the fields of any configuration record (`Turing.joinFields_cfgRecord_length`) gives the joined length as $k(2s+1)+\mathrm{posWidth}(x.length)+k+4$. Substituting $x.length=n$ yields the claimed expression.

**Key facts.** `Turing.joinFields_cfgRecord_length`.
