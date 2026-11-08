<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.pmfInner_self_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Probability Inner Product

**Claim.** For a finite set Ω, a probability distribution π on Ω, and a function f: Ω → ℝ, the probability inner product satisfies 0 ≤ ⟨f,f⟩π.

**Proof.** By the expectation formula for the inner product (FABL.pmfInner_eq_expect), ⟨f,f⟩π is the expectation of the function x ↦ f(x)². Each value is nonnegative because it is a square. The nonnegativity of expectation for a pointwise nonnegative function (FABL.pmfExpectation_nonneg) therefore gives the result.

**Key facts.** `FABL.pmfInner_eq_expect`, `FABL.pmfExpectation_nonneg`.
