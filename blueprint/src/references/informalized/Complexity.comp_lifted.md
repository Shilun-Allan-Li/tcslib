<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_lifted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifted Output Oracle Answers

**Claim.** The lifted oracle on the nested encoding returns the length test for $f(x)$ in length mode and the indexed bit of $f(x)$ otherwise.

**Proof.** Split on the Boolean mode. In either case the query is exactly the nested encoded query covered by the lifted-query identity (\texttt{compLift\_query}); specializing that identity to the selected mode gives the stated length test or output bit.

**Key facts.** `Complexity.compLift_query`.
