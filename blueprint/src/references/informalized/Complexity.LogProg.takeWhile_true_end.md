<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean :: Complexity.LogProg.takeWhile_true_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entry After the Initial True Run

**Claim.** For every Boolean list $x$, the entry immediately after its initial run of true entries is either absent or false.

**Proof.** Induct on the list. For the empty list the indexed entry is absent. For a list beginning with false, the initial true run has length zero, and the entry at that index is the first, false entry. If the list begins with true, its initial true run consists of that first entry followed by the initial true run of the tail. The entry immediately after this longer run is therefore the entry immediately after the tail's initial true run; the induction hypothesis says it cannot be true.
