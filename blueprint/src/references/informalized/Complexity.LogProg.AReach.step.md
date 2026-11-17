<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.AReach.step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending a Reachability Step

**Claim.** If $G$ holds at $a$ and a finite run from the one-step successor of $a$ reaches $c$ while satisfying $G$ before its endpoint, then a finite run from $a$ reaches $c$ with the same condition.

**Proof.** The one-step reachability lemma (`Complexity.LogProg.AReach.single`) gives a run from $a$ to its one-step successor, and its only pre-endpoint configuration is $a$, where $G$ holds by hypothesis. Concatenate this run with the given run using transitivity of constrained reachability (`Complexity.LogProg.AReach.trans`).

**Key facts.** `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.trans`.
