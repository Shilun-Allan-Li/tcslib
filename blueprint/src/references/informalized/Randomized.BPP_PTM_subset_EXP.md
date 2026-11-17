<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.BPP_PTM_subset_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP Is Contained in EXP

**Claim.** Every language decidable by a bounded-error randomized Turing machine in polynomial time belongs to EXP.

**Proof.** Take a language in the polynomial-time randomized class. The class-to-machine translation gives a polynomial-time BPP model for that language (`Randomized.inBPP_of_mem_BPP_PTM`). The deterministic exponential-time simulation theorem then places every language accepted by such a model in EXP (`Randomized.mem_EXP_of_inBPP_polyTimeModel`). This is the formal proof's route; the detailed simulation is supplied by that theorem.

**Key facts.** `Randomized.inBPP_of_mem_BPP_PTM`, `Randomized.mem_EXP_of_inBPP_polyTimeModel`.
