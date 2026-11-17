<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.Reaches.refl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of reaching

**Claim.** A configuration $c_0$ reaches itself relative to any reference configuration $c$, register $r$, and position $p$.

**Proof.** Choose the reaching time to be $0$. Running for zero steps leaves $c_0$ unchanged, so the endpoint condition holds. There are no intermediate times $t<0$, so the requirement on intermediate configurations is vacuous.
