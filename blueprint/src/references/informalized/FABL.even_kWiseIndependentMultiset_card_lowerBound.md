<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/KWiseIndependentLowerBound.lean :: FABL.even_kWiseIndependentMultiset_card_lowerBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Independence Support Bound

**Claim.** For an even-wise independent multiset on the sign cube, the sum of the binomial coefficients through degree $k/2$ is at most the size of its underlying finite sample space.

**Proof.** Choose a frequency family whose elements pairwise have union of size at most $k$ and whose cardinality is $\sum_{j=0}^{k/2}\binom nj$; such a family exists when $k$ is even (`exists_even_kWiseFrequencyFamily`). The $k$-wise independence hypothesis bounds the cardinality of this family by the size of the sample space (`card_frequencyFamily_le_card_of_isKWiseIndependentMultiset`). Substituting the chosen family’s cardinality gives the claimed lower bound.

**Key facts.** `FABL.exists_even_kWiseFrequencyFamily`, `FABL.card_frequencyFamily_le_card_of_isKWiseIndependentMultiset`.
