<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.length_clearF₂PivotRows -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length preservation under pivot clearing

**Claim.** Clearing the pivot from each equation in a finite list of linear equations over $\mathbb{F}_2$ preserves the list's length.

**Proof.** Pivot clearing is applied separately to each equation by mapping a function over the input list. A map changes the entries but preserves the number of list positions, so the resulting list has the same length as the original.
