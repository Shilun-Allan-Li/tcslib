<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilyTotalRandomExamples_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total random examples bound

**Claim.** The total number $|\mathcal{F}|N$ of random examples is at most $16|\mathcal{F}|^3L/\varepsilon^2$.

**Proof.** Use the per-coefficient estimate to bound $N$ by $16|\mathcal{F}|^2L/\varepsilon^2$ (`finiteFamilySamplesPerCoefficient_cast_le`). Multiplying both sides by the nonnegative family size preserves the inequality, and collecting the powers gives $16|\mathcal{F}|^3L/\varepsilon^2$.

**Key facts.** `FABL.finiteFamilySamplesPerCoefficient_cast_le`.
