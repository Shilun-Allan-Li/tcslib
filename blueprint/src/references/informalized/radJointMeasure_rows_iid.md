<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: radJointMeasure_rows_iid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independence of Rademacher Rows

**Claim.** The row-valued random variables of the joint Rademacher array are mutually independent.

**Proof.** The joint array measure is a product over row indices, with each factor the space of rows equipped with its $d$-fold product Rademacher measure. For a product measure, the coordinate projections into the factors are mutually independent. Here those projections are exactly the row-valued random variables, so the rows are mutually independent.
