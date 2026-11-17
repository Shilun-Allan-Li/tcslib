<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.RL_subset_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Logspace Is Contained in Polynomial Time

**Claim.** Every language decidable by a randomized Turing machine using logarithmic space, halting on every input within some finite input-dependent number of steps, with acceptance probability at least $2/3$ on members and no accepting branch on nonmembers, is decidable by a deterministic Turing machine in polynomial time.

**Proof.** First use the containment of randomized logspace in nondeterministic logspace (`Randomized.RL_subset_NL`). Then apply the containment of nondeterministic logspace in polynomial time (`Complexity.NL_subset_P`). Composing these inclusions proves the result.

**Key facts.** `Randomized.RL_subset_NL`, `Complexity.NL_subset_P`.
