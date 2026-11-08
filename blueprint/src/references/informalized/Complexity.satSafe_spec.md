<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satSafe_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safe Request Representation

**Claim.** For every Boolean word $z$, there are a CNF formula $\varphi$ and a Boolean word $u$ such that the safe request is the pairing of the serialization of $\varphi$ with $u$, every variable index in $\varphi$ is less than $|u|$, and evaluating $\varphi$ using $u$ (with out-of-range variables false) gives the safe evaluation value of $z$.

**Proof.** Split according to whether the goodness check on $z$ succeeds. If it fails, use the empty formula and empty word: the safe request is the fixed encoding of this fallback pair, and both the variable-bound and evaluation claims reduce to the definitions of the empty formula and the safe fallback value. If goodness succeeds, the split search cannot fail, since validity of the split is one of the conditions in the goodness check. Let $i$ be the successful split point. The syntax check on the first component, together with the characterization of syntactic validity by successful parsing (`CNF.syntaxOK_spec`), ensures that parsing $z$’s prefix of length $i$ yields some formula $\varphi$. The parse reconstruction theorem gives that this prefix is exactly the serialization of $\varphi$, so take $u=z$ with its first $i$ bits removed. The split equation gives $|u|=i+1$, while the decoded formula’s number of variables is at most the prefix length (`CNF.numVars_decode_le`). Every literal variable index is below the formula’s number of variables (`sat_literal_lt_numVars`), and therefore below $|u|$. The safe-request equality follows from the split and parse reconstruction; decoding the paired request recovers the prefix and suffix by `pairDecode_pairEncode`. The same decoding identity and the formula-decoding equality show that evaluating the decoded formula on the suffix assignment is exactly the value used by the successful safe-evaluation branch.

**Key facts.** `Std.Sat.CNF.syntaxOK_spec`, `Turing.pairDecode_pairEncode`, `Std.Sat.CNF.parse_repr`, `Complexity.sat_split_some`, `Std.Sat.CNF.numVars_decode_le`, `Complexity.sat_literal_lt_numVars`.
