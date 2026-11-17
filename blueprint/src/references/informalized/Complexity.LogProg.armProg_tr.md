<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean :: Complexity.LogProg.armProg_tr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Function of the Compiled Program

**Claim.** The compiled register program's transition at state $(l,ph)$ with scanned symbols $a$ and $w$ is exactly the action prescribed by instruction $A(l)$ at label $l$, phase $ph$, and those scanned symbols.

**Proof.** Unfold the compiled program's transition function. Its transition at $(l,ph)$ is defined by the instruction-transition function applied to $A(l)$, $l$, $ph$, $a$, and $w$. This is the asserted action.
