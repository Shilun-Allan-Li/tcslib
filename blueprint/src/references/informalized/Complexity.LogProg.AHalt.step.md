<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.AHalt.step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending One Step to Guarded Halting

**Claim.** If $G$ holds of configuration $a$ and the run from its one-step successor halts with answer $r$ while satisfying $G$ before halting, then the run from $a$ also halts with answer $r$ and satisfies $G$ before halting.

**Proof.** The one-step reachability fact (`Complexity.LogProg.AReach.single`) says that $a$ reaches its successor in one step, with $G$ holding at every time before that endpoint; the sole such configuration is $a$, where $G$ holds by assumption. Concatenating this guarded reachability with the given guarded halting run (`Complexity.LogProg.AReach.halt`) yields a run from $a$ that halts with the same answer and satisfies $G$ at every time before halting.

**Key facts.** `Complexity.LogProg.AReach.single`, `Complexity.LogProg.AReach.halt`.
