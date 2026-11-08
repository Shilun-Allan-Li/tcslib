<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.RL_subset_BPL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Logspace Is Contained in Bounded-Error Logspace

**Claim.** Every language of Boolean strings decidable in randomized logspace with one-sided error is decidable in bounded-error randomized logspace, with a constant-factor logspace machine that halts within a finite time bound on every input and outputs the correct membership bit with probability at least $2/3$.

**Proof.** Apply the general inclusion of randomized space with one-sided error in bounded-error randomized space, taking the space function to be logarithmic space (`Randomized.RSPACE_subset_BPSPACE`). By the definitions of $RL$ and $BPL$, this is exactly the stated inclusion.

**Key facts.** `Randomized.RSPACE_subset_BPSPACE`.
