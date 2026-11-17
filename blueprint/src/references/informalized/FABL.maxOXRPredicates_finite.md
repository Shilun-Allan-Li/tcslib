<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.maxOXRPredicates_finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finiteness of maximum OXR predicates

**Claim.** The family of maximum OXR predicates is finite.

**Proof.** Every maximum OXR predicate is obtained by choosing a Boolean sign pattern on three inputs and applying `oxrPredicate.negateInputs` to it. The family is therefore contained in the range of a function whose domain, the set of Boolean patterns on three positions, is finite. Its range, and hence the predicate family, is finite.
