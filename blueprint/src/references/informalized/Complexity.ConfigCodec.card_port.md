<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.ConfigCodec.card_port -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cardinality of the port set

**Claim.** For every natural number $k$, the port set for $k$ work tapes has cardinality $3k+7$.

**Proof.** Replace the port type by its proxy type through the cardinality-preserving equivalence supplied by `Port.proxyTypeEquiv`. The proxy type separates the ports into finite summands, so its cardinality is the sum of their sizes. Simplifying that sum gives $3k+7$, as required.
