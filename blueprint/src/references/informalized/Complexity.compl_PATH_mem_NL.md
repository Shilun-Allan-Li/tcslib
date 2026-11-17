<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean :: Complexity.compl_PATH_mem_NL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement of PATH Lies in NL

**Claim.** The complement of PATH belongs to NL, the class of languages decidable by a finite nondeterministic Turing machine in logarithmic space.

**Proof.** PATH belongs to NL by the PATH membership theorem (PATH_mem_NL). Nondeterministic log space is closed under complement (compl_mem_NL), so applying that closure result to PATH gives $\mathrm{PATH}^{c}\in\mathrm{NL}$.

**Key facts.** `Complexity.PATH_mem_NL`, `Complexity.compl_mem_NL`.
