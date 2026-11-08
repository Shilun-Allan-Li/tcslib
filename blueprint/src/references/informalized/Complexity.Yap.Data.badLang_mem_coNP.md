<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.Data.badLang_mem_coNP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad Language Is in coNP

**Claim.** If $d$’s language $R$ belongs to polynomial time, then the language of strings satisfying $d$’s check for every polynomially bounded auxiliary string belongs to coNP.

**Proof.** By definition, the complement of the bad language consists of inputs for which there exists an auxiliary string of length at most $d.B(|p|+1)^{d.b}$ that fails the check. Use this auxiliary string as the polynomially bounded NP witness. The check language is in polynomial time under the assumption on $R` (`Complexity.Yap.Data.checkLang_mem_P`), so its complement is also in polynomial time (`Complexity.compl_mem_P`). The polynomially bounded-witness characterization of NP (`Complexity.mem_NP_iff_exists_length_le`) now places the complement of the bad language in NP. The witness test is exactly nonmembership in the check language: decoding the encoded pair recovers its two components (`Complexity.pairFstD_pairEncode` and `Complexity.pairSndD_pairEncode`), and the defining check-language equivalence (`Complexity.Yap.Data.mem_checkLang`) identifies that test with the required check. Hence the bad language is in coNP.

**Key facts.** `Complexity.Yap.Data.checkLang_mem_P`, `Complexity.compl_mem_P`, `Complexity.mem_NP_iff_exists_length_le`, `Complexity.Yap.Data.mem_checkLang`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
