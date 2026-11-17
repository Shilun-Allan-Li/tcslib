<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaPolynomialSamples_ideal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ideal Polynomial Sample List

**Claim.** The polynomial sample list extracted from the labeled restriction batch has, at each position, the reindexed input chosen at that position together with the value of the reindexed restriction on that input.

**Proof.** Fix a position $i$. By definition, the polynomial sample list takes the labeled batch entry at the polynomial sample index and reindexes its input using the fixed-sign-cube equivalence. The labeled batch pairs each free assignment with the value of the restriction at that assignment. After reindexing, this label is exactly the reindexed restriction evaluated at the resulting input. Thus the entries agree at every position, and extensionality gives equality of the lists as functions.
