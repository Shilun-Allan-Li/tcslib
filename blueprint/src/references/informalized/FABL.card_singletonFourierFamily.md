<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.card_singletonFourierFamily -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the singleton Fourier family

**Claim.** For every natural number $n$, the family of singleton subsets of the $n$ coordinate indices has cardinality $n$.

**Proof.** Send each coordinate index $i$ to its singleton set $\{i\}$. This map is injective, since equal singleton sets have equal elements. Thus the family of singleton sets has the same cardinality as the full set of coordinate indices, which is $n$.
