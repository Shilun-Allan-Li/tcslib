<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.TQBF_PSPACEComplete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# TQBF PSPACE-Completeness

**Claim.** The language of bit strings whose decoded quantified Boolean formula is true is PSPACE-complete: it belongs to PSPACE, and every language in PSPACE has a polynomial-time many-one reduction to it.

**Proof.** By the membership theorem, TQBF belongs to PSPACE (Complexity.TQBF_mem_PSPACE). By the hardness theorem, every language in PSPACE has a polynomial-time many-one reduction to TQBF (Complexity.TQBF_PSPACEHard). PSPACE-completeness is the conjunction of these two properties, so TQBF is PSPACE-complete.

**Key facts.** `Complexity.TQBF_mem_PSPACE`, `Complexity.TQBF_PSPACEHard`.
