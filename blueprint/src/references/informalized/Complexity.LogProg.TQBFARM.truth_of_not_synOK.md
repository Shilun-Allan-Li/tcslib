<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.truth_of_not_synOK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth When the Syntax Check Fails

**Claim.** If the syntax check of a bit string $x$ returns false, then the quantified Boolean formula decoded from $x$ is true.

**Proof.** Split according to the result of aligned-pair decoding. If decoding fails, the decoder uses the empty quantifier prefix and empty CNF fallback matrix; that matrix is true under every assignment, and therefore remains true under any quantifier prefix by `truthAux_nil`. If decoding succeeds with components $(q,m)$, the syntax-check specification (`synOK_spec`) and the assumed false result imply that $m$ does not parse as a CNF formula. Hence its CNF decoder also uses the empty fallback matrix. The decoded formula has the quantifier prefix obtained from $q$, and again `truthAux_nil` shows that this prefix quantifying the empty matrix is true.

**Key facts.** `Complexity.LogProg.TQBFARM.synOK_spec`, `Complexity.LogProg.TQBFARM.truthAux_nil`.
