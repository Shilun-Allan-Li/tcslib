<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean :: Complexity.BinArith.slotsLe_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-Bounded Decoded Slots

**Claim.** For every finite bit string $W$, each of the four decoded slots listed in the statement has length at most $|W|$.

**Proof.** The first slot has length at most $|W|$ by the bound on the length of the first decoded component (`Complexity.length_pairFstD_le`). For the other slots, use the corresponding bound on the second decoded component (`Complexity.length_pairSndD_le`): the second component of $W$ has length at most $|W|$, and the second component of that component has length at most its own input length. Applying the first-component bound to each of these inputs gives the remaining three inequalities by transitivity.

**Key facts.** `Complexity.length_pairFstD_le`, `Complexity.length_pairSndD_le`.
