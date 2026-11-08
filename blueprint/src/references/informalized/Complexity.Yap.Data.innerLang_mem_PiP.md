<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.Data.innerLang_mem_PiP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Language Lies in the Second Universal Class

**Claim.** If $d$’s language $R$ is in polynomial time, then the language of strings $w$ such that every string $t$ has $w,t$ outside the bad language lies in the second universal class of the polynomial hierarchy.

**Proof.** To show membership in the second universal class, it suffices to show that the complement of the inner language is in the second existential class. The complement condition says that some string $t$ has $w,t$ in the bad language. This is already a polynomially bounded existential witness over the first universal class: the bad language belongs to coNP by `Complexity.Yap.Data.badLang_mem_coNP`, and the first universal class is coNP (`Complexity.PiP_one`). The successor-level characterization (`Complexity.Yap.mem_SigmaP_succ_of_exists_le`) applies once the witness length bound and witness relation are provided. For any such witness, membership in the bad language forces the core length requirement: instantiate its universal check condition with the empty auxiliary string, whose length is within the permitted bound. By `Complexity.Yap.Data.mem_badLang`, this yields the required bound on $t$. Conversely, any witness satisfying that bound and belonging to the bad language directly witnesses failure of the universal condition defining the inner language (`Complexity.Yap.Data.mem_innerLang`). Thus the complement is in the second existential class, which is the desired second universal-class conclusion.

**Key facts.** `Complexity.PiP_one`, `Complexity.Yap.Data.badLang_mem_coNP`, `Complexity.Yap.mem_SigmaP_succ_of_exists_le`, `Complexity.Yap.Data.mem_innerLang`, `Complexity.Yap.Data.mem_badLang`.
