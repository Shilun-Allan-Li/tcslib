<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.runWith_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenating Computation Sequences

**Claim.** Running on the concatenation $w w'$ from $c$ gives the same configuration as first running on $w$ from $c$ and then on $w'$ from the resulting configuration.

**Proof.** Induct on $w$, generalizing the starting configuration $c$. When $w$ is empty, running on the concatenation is just running on $w'$, as claimed. For $w=b::v$, expand both runs beginning with a bit using the one-step expansion of `runWith` (`Turing.OracleNDTM.runWith_cons`). The concatenated sequence becomes $b::(v++w')$; after its first step, the induction hypothesis applied to $v$ and the resulting configuration identifies the remaining run with running first on $v$ and then on $w'$. Reassembling the first step gives the desired equality.

**Key facts.** `Turing.OracleNDTM.runWith_cons`.
