<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.RL_subset_NL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized Logspace Is Contained in Nondeterministic Logspace

**Claim.** Every language decidable by a randomized Turing machine using logarithmic space, halting on every input within some finite input-dependent number of steps, with acceptance probability at least $2/3$ on members and no accepting branch on nonmembers, is decidable by a nondeterministic Turing machine using logarithmic space.

**Proof.** Use the general containment of randomized space with one-sided error in nondeterministic space, instantiated with logarithmic space (`Randomized.RSPACE_subset_NSPACE`). The definitions of $RL$ and $NL$ then give the asserted containment.

**Key facts.** `Randomized.RSPACE_subset_NSPACE`.
