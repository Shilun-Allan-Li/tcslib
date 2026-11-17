<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.Reach.single' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability from One Guarded Step

**Claim.** If a configuration at label $l$ with registers $v$ satisfies the guard and one computation step takes it to label $l'$ with registers $v'$, then the latter configuration is reachable from $(l,v)$ with the guard holding at every earlier step.

**Proof.** The one-step reachability principle (`AReach.single`) says that any guarded configuration reaches its immediate successor in one step, with the guard required at the initial time. Apply it to the configuration $(l,v)$ and the stated guard. Its endpoint is the result of one computation step; the given step equation identifies that endpoint with $(l',v')$. Hence this witness is exactly the required reachability.

**Key facts.** `Complexity.LogProg.AReach.single`.
