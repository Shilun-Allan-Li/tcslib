<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseOutputMultiset_card_eq_two_pow_randomBits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Multiset Cardinality

**Claim.** For an almost-wise input, the output multiset has cardinality $2^r$, where $r$ is the number of random bits specified by the input.

**Proof.** The output multiset is obtained by viewing the output list as a multiset, so its cardinality is the length of that list. The output-list length formula (`almostKWiseOutputList_length`) gives length $2^{2d}$, where $d$ is the field degree of the associated small-bias input. By definition, the number of random bits is $2d$. Substitution yields the claimed cardinality.

**Key facts.** `FABL.almostKWiseOutputList_length`.
