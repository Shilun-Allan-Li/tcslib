<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/QueryLearning.lean :: FABL.measure_finiteFamily_someCoefficientBadSetWithTotalConfidence_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total-confidence coefficient bound

**Claim.** For a nonempty finite family, choosing per-coefficient confidence as $\delta/|\mathcal F|$ makes the probability that any coefficient estimate is bad at most $\delta$.

**Proof.** Apply the finite-family union estimate (`FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le`), which bounds the probability by $|\mathcal F|$ times the per-coefficient confidence. By its definition, that confidence equals $\delta/|\mathcal F|$. Since the family is nonempty, its cardinality is positive, and the product simplifies to $\delta$.

**Key facts.** `FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le`.
