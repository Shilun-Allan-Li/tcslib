<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.TQBF_PSPACEHard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# PSPACE Hardness of TQBF

**Claim.** TQBF is PSPACE-hard: every language in PSPACE has a polynomial-time many-one reduction to the language of bit strings whose decoded quantified Boolean formula is true.

**Proof.** Take any language $L$ in PSPACE. The reduction theorem for quantified Boolean formulas gives a polynomial-time many-one reduction from $L$ to the language of true decoded quantified Boolean formulas (the fact stated by `PSPACE_polyTimeReducible_TQBF`). Since this target language is exactly TQBF, the required reduction follows. As this holds for every $L$ in PSPACE, TQBF is PSPACE-hard.

**Key facts.** `Complexity.TQBFHard.PSPACE_polyTimeReducible_TQBF`.
