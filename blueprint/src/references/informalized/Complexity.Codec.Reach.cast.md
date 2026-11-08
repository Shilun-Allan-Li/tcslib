<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.Reach.cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reachability Under Endpoint Recasting

**Claim.** If the compiled computation reaches label $l_2$ with registers $v_2$ from label $l_1$ with registers $v_1$, satisfying the guard at every earlier step, and $v_2=v_2'$, then it also reaches $l_2$ with registers $v_2'$ under the same guard and from the same initial configuration.

**Proof.** Reachability records an endpoint configuration together with a computation length and the guard at every earlier time. Replacing the endpoint register assignment by an equal assignment does not change that endpoint configuration: the label and initial configuration are unchanged, and $v_2=v_2'$. Thus the same computation length and the same earlier guard witnesses prove the recast reachability statement.
