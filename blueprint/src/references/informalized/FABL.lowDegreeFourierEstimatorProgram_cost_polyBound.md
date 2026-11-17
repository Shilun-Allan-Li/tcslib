<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.lowDegreeFourierEstimatorProgram_cost_polyBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial cost bound for the low-degree estimator

**Claim.** Every supported outcome of the low-degree estimator satisfies the stated bounds on random examples and charged work, and makes zero membership queries.

**Proof.** Use the finite-family estimator’s polynomial cost bound with the family consisting of all subsets of $[n]$ of size at most $k$. This family is nonempty, so the bound applies. Its random-example and work estimates are precisely the asserted expressions after substituting this family for the general finite family; the membership-query count is zero. The conclusion follows directly from that bound.

**Key facts.** `FABL.finiteFamilyFourierEstimatorProgram_cost_polyBound`, `FABL.lowDegreeFourierFamily_nonempty`.
