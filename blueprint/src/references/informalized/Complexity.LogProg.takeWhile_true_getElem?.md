<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.takeWhile_true_getElem? -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries Within the Initial True Run

**Claim.** For every Boolean list $x$ and natural number $c$, if $c$ is less than the length of the initial run of true entries in $x$, then the entry of $x$ at index $c$ is present and true.

**Proof.** Induct on the list, keeping the index arbitrary. The empty list and a list beginning with false have no index below the length of their initial true run. If the list begins with true, index zero is true directly. For a positive index, remove the first entry and decrease the index by one. The assumed bound then says the decreased index lies within the tail's initial true run, so induction gives a present true entry there; shifting back one position proves the claim for the original list.
