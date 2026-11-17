<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.TQBF_mem_PSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# TQBF Lies in PSPACE

**Claim.** The language of bit strings that decode to true quantified Boolean formulas is decidable by a finite Turing machine using at most $c(n^c+1)$ work-tape cells on inputs of length $n$, for some natural number $c$.

**Proof.** The result follows directly from `truth_mem_PSPACE`, which establishes that the language of bit strings whose decoded quantified Boolean formula is true belongs to PSPACE. By the definition of PSPACE in this development, membership supplies a natural number $c$ and a finite Turing machine deciding the language within the space bound $c(n^c+1)$.

**Key facts.** `Complexity.LogProg.TQBFARM.truth_mem_PSPACE`.
