<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productInfluence_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Product Influence

**Claim.** For a finite state space with a probability distribution, the product influence of a real-valued function at every coordinate is nonnegative.

**Proof.** The influence is the inner product of the coordinate difference with itself. The inner product of a function with itself under a probability distribution is nonnegative (`pmfInner_self_nonneg`), so the influence is nonnegative.

**Key facts.** `FABL.pmfInner_self_nonneg`.
