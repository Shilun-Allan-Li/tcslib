<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPoly.lean :: BoolCircuit.mem_PPoly_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Circuit Size

**Claim.** A Boolean language belongs to the class of languages recognized by polynomial-size, fan-in-two circuits exactly when some such circuit family recognizes the language and has size at most $a(n+1)^k$ for natural numbers $a$ and $k$.

**Proof.** By definition, $\mathrm{PPoly}$ is the set of languages satisfying $\mathrm{InPPoly}$. Membership in this set is therefore equivalent directly to $L\in\mathrm{InPPoly}$, which is the stated polynomial-size circuit-family condition.
