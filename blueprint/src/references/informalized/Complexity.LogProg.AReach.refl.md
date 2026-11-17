<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.AReach.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of Guarded Reachability

**Claim.** For every configuration $a$, the run from $a$ reaches $a$ at some time, with $G$ holding at every configuration before that time.

**Proof.** Choose time $T=0$. The run is at $a$ at time zero, and there are no natural numbers $t<0$. Thus the guard condition is vacuous, regardless of $G$.
