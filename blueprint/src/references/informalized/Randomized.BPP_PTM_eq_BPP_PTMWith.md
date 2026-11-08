<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.BPP_PTM_eq_BPP_PTMWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard and Threshold-Based BPP

**Claim.** The standard polynomial-time BPP class equals the class defined by requiring correctness probability at least $2/3$ on every input.

**Proof.** The equality is definitional: the standard class uses the same polynomial-time randomized machines and the same correctness lower bound $2/3$ on every input as the constant-threshold class. Unfolding the two definitions therefore gives identical membership conditions.
