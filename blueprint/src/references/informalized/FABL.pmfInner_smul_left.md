<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.pmfInner_smul_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar Multiplication in the First Argument

**Claim.** For a finite set Ω, a probability distribution π, a scalar c ∈ ℝ, and functions f,g: Ω → ℝ, one has ⟨cf,g⟩π = c⟨f,g⟩π.

**Proof.** Express each inner product as an expectation (FABL.pmfInner_eq_expect). Pointwise, (c f(x))g(x) = c(f(x)g(x)), by associativity and commutativity of real multiplication. Pulling the constant c outside the expectation using linearity under constant multiplication (FABL.pmfExpectation_const_mul) gives the claimed identity.

**Key facts.** `FABL.pmfInner_eq_expect`, `FABL.pmfExpectation_const_mul`.
