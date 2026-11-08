<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.evalMultilinearRV_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of Multilinear Random Evaluation

**Claim.** For independent random variables each in $L^4$, the multilinear random evaluation with any real coefficient family belongs to $L^4$.

**Proof.** This declaration follows directly from the natural-exponent integrability theorem (`evalMultilinearRV_memLp_nat`): apply it with the natural exponent $p=4$, which is positive, and with the given coefficient family, independent random variables, and their $L^4$ hypotheses. Its conclusion is exactly the asserted $L^4$ membership.

**Key facts.** `BooleanAnalysis.Hypercontractivity.evalMultilinearRV_memLp_nat`.
