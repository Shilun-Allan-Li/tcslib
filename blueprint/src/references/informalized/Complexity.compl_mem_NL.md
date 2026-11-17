<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountGenCorrect.lean :: Complexity.compl_mem_NL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Closure of Nondeterministic Log Space

**Claim.** If a binary language is decidable by a finite nondeterministic Turing machine using at most a constant multiple of logarithmic space, then its complement is also decidable within such a bound.

**Proof.** Apply the complement-closure theorem for nondeterministic space with the space function equal to logarithmic space itself. Its required pointwise inequality is equality, so the theorem carries the given NL membership directly to the complement, establishing membership in NL.

**Key facts.** `Complexity.compl_mem_NSPACE`.
