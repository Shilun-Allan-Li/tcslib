<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerVerifier.lean :: Complexity.Meyer.innerLang_mem_coNP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CoNP membership of the inner language

**Claim.** For the given constants and machine, the language requiring every Boolean string $v$ to make the encoded pair avoid the bad language belongs to coNP.

**Proof.** By the characterization of coNP, it suffices to show that the complement has polynomially bounded certificates verifiable in polynomial time. The verifier can be the bad language itself, which is in P (`badLang_mem_P`). By the length-bounded NP characterization (`mem_NP_iff_exists_length_le`), it remains to supply a polynomial-size witness exactly when some $v$ makes the pair encoding bad.

Given such a counterexample $v$, set $z$ to the pair encoding of the input word $w$ and $v$. Extract from $z$ the four decoded components used by the atom evaluator: the time, address, index, and payload fields. Encode those components together into a witness $u$ using nested pair encodings. The pair-decoding identities ensure that, when the verifier evaluates atoms on the pair encoding of $w$ and $u$, all six decoded fields agree with those extracted from $z$. The congruence principle for atom evaluation (`evalAtom_congr`) therefore makes every atom value identical, so the badness of $z$ transfers to the new encoding.

It remains to bound the witness length. Since $z$ is a bad encoding, its length-field check gives the prescribed bounds on the time, address, index, and payload components. In particular, the payload length is bounded by the width determined by the input component. The input component extracted from $z$ has length at most $|w|$ (`length_pairFstD_le`), and the width function is monotone in that length, so the width is at most $C_w(|w|+1)^{c_w}$. The index bound and the width bounds then bound each component in the nested encoding; using the length formula for pair encoding (`Turing.length_pairEncode`) yields a total witness length at most $(7C_w+12)(|w|+1)^{c_w+1}$. Thus every complement member has a polynomial-size certificate. Conversely, any witness accepted by this verifier directly supplies a counterexample to the universal condition, giving the required equivalence.

**Key facts.** `Complexity.Meyer.badLang_mem_P`, `Complexity.mem_NP_iff_exists_length_le`, `Complexity.Meyer.evalAtom_congr`, `Complexity.pairFstD_pairEncode`, `Complexity.length_pairFstD_le`, `Turing.length_pairEncode`.
