<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinBasic.lean :: CommunicationComplexity.PublicCoin.Protocol.rrun_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized and Paired-Input Runs

**Claim.** For every input pair and coin outcome, the randomized execution of a public-coin protocol equals the deterministic execution on the paired inputs.

**Proof.** The randomized run is defined to be the deterministic protocol's run with Alice's input $(\omega,x)$ and Bob's input $(\omega,y)$. The two sides are therefore equal by definition.
