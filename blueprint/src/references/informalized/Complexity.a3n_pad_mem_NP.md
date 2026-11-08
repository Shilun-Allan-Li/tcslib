<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_pad_mem_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Padding Preserves NP Membership

**Claim.** If $V$ is in polynomial time and membership in $L$ is characterized by a certificate of length $C(2^{|x|+1})^c$ whose concatenation with $x$ lies in $V$, then the language of pair encodings of $x$ with the prescribed all-ones padding, for $x\in L$, belongs to NP.

**Proof.** Use the length-bounded-certificate characterization of NP (`Complexity.mem_NP_iff_exists_length_le`) with the verifier supplied by `Complexity.a3n_verifier_mem_P`. Its verifier checks that the input decodes as an outer pair whose first component is itself a pair $(x,pad)$, that $pad$ is the required all-ones word, that the supplied witness has length $C2^{(|x|+1)^c}$, and that $x$ concatenated with the witness belongs to $V$. The verifier is in polynomial time because $V$ is, as asserted by `Complexity.a3n_verifier_mem_P`. For completeness, take any encoded padded word arising from an $x\in L$. The hypothesis provides a witness $u$ of the required length with $x u\in V$. The outer pair encoding with witness $u$ has the required polynomially bounded certificate length, and decoding the nested pair recovers the padded word and $u$ (`Turing.pairDecode_pairEncode`), so the verifier accepts. For soundness, suppose some witness makes the verifier accept on $z$. Decoding the outer pair yields a nested pair $(x,pad)$ and a witness $u$; the verifier guarantees the prescribed padding, the required witness length, and $x u\in V$. The pair-decoding inverse (`Complexity.a3n_pair_inverse`) identifies $z$ with the encoding of that decoded $(x,pad)$. The certificate hypothesis then implies $x\in L$, and the padding equality shows that $z$ is exactly the designated padded encoding for this $x$. Thus every accepted input belongs to the padded language.

**Key facts.** `Complexity.mem_NP_iff_exists_length_le`, `Complexity.a3n_verifier_mem_P`, `Turing.pairDecode_pairEncode`, `Complexity.a3n_pair_inverse`.
