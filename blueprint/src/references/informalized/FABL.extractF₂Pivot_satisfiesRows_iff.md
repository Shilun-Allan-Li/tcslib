<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.extractF₂Pivot_satisfiesRows_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction After Pivot Extraction

**Claim.** For any assignment of values in $\mathbb F_2$ to the variables, all equations in the original list are satisfied exactly when the extracted pivot and every equation in the remaining list are satisfied.

**Proof.** Induct on the original list. In the case where the head equation has coefficient $1$ at the chosen variable, extraction returns that head as pivot and leaves the tail as remainder. The assertion then says exactly that satisfying every equation in the list is equivalent to satisfying the head and every equation in the tail. In the other case, extraction succeeds recursively on the tail. Apply the induction hypothesis to the tail: satisfaction of every tail equation is equivalent to satisfaction of the recursively extracted pivot and its remainder. The original remainder consists of the skipped head followed by that recursive remainder. Requiring satisfaction of the head as well therefore gives precisely the equivalence claimed for the original list.
