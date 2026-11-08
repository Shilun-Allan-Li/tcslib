<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/Rademacher.lean :: variance_id_rademacherReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of the Rademacher Variable

**Claim.** The identity random variable under the symmetric Rademacher measure has variance $1$.

**Proof.** The identity variable is square-integrable since it lies almost surely in $[-1,1]$ (rademacherReal_mem_Icc). Its second moment is $1$ (integral_sq_rademacherReal), while its mean is $0$ (integral_id_rademacherReal). The variance, second moment minus the square of the mean, is therefore $1-0^2=1$.

**Key facts.** `rademacherReal_mem_Icc`, `integral_sq_rademacherReal`, `integral_id_rademacherReal`.
