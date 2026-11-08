<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinBasic.lean :: CommunicationComplexity.PrivateCoin.Protocol.rrun_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired-input execution

**Claim.** For every private-coin protocol and every pair of inputs and coin outcomes, its randomized execution equals its deterministic run on the corresponding paired inputs.

**Proof.** By definition, randomized execution of $p$ on $x,y$ with coin outcomes $\omega_x,\omega_y$ is the deterministic run of $p$ on $(\omega_x,x)$ and $(\omega_y,y)$. The two sides are therefore identical.
