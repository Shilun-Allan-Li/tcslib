<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.extractF₂Pivot_forall_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Predicates Under Pivot Extraction

**Claim.** If extraction returns a pivot equation and a remaining list, then every equation in the original list satisfies a predicate exactly when the pivot and every equation in the remaining list satisfy it.

**Proof.** Induct on the original list. For a nonempty list, if its head has coefficient $1$ at the chosen variable, extraction returns that head as pivot and the untouched tail as remainder. The claim is then precisely the decomposition of the universal condition over head and tail. If the head's coefficient is not $1$, extraction recurses on the tail. A successful recursive extraction returns a pivot and a remainder; the induction hypothesis identifies the universal condition on the tail with the condition on that pivot and remainder. The original remainder consists of the head followed by the recursive remainder, so adding the head's predicate condition on both sides yields the stated equivalence.
