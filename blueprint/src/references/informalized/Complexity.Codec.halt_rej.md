<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Parse.lean :: Complexity.Codec.halt_rej -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reaching rejection gives a rejecting halt

**Claim.** If the codec machine reaches its rejection label under the execution guard and the resulting registers remain bounded by $B$, then it halts with answer false from the original configuration, with the guard holding before halting.

**Proof.** At the reached rejection configuration, the machine's instruction is to return false. The register bound hypothesis supplies the register part of the guard there, and the guard's instruction-specific condition holds at the rejection label. Thus the return instruction gives a false-answer halt from that configuration (`AHalt.ret`). Composing this halt with the guarded reachability path (`AReach.halt`) yields the required halt from the original configuration; the reachability premise supplies the guard along the path before arrival.

**Key facts.** `Complexity.LogProg.AHalt.ret`, `Complexity.LogProg.AReach.halt`.
