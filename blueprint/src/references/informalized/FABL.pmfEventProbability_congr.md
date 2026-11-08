<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfEventProbability_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalent Events Have Equal Probability

**Claim.** If two predicates on a finite probability space hold for exactly the same elements, then they have equal probability.

**Proof.** The pointwise equivalence of the predicates makes their indicator functions equal at every element: each takes value $1$ when its predicate holds and $0$ otherwise. Hence the expectation of one indicator equals the expectation of the other, which is precisely equality of the two event probabilities.
