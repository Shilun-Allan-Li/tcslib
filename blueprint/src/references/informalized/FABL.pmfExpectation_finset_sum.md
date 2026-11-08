<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.pmfExpectation_finset_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a finite sum

**Claim.** The expectation of a finite sum of real-valued functions on a finite probability space is the sum of their expectations.

**Proof.** Expand the expectation using its defining finite sum over outcomes. For each outcome, distribute its probability weight across the finite sum of functions. Interchanging the two finite sums then groups together, for each index, the weighted values over all outcomes. Each grouped sum is the expectation of the corresponding function, proving the identity.
