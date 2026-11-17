<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean :: Complexity.PATH_mem_NL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Directed Reachability Lies in NL

**Claim.** The language of binary encodings of finite directed graphs with a target reachable from the designated start belongs to $\mathrm{NL}$.

**Proof.** The equality `PATH_eq_pathRawLang` identifies the matrix encoding of directed reachability with the raw-list encoding. Under this identification, the theorem `pathRawLang_mem_NL` supplies a nondeterministic log-space decider for the language. Rewriting the language by the encoding equality therefore proves that $\mathrm{PATH}\in\mathrm{NL}$.

**Key facts.** `Complexity.PATH_eq_pathRawLang`, `Complexity.pathRawLang_mem_NL`.
