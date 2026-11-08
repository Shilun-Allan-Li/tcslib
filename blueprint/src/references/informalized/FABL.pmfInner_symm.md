<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.pmfInner_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the Probability Inner Product

**Claim.** For a finite set Ω, a probability distribution π, and functions f,g: Ω → ℝ, the probability inner product is symmetric: ⟨f,g⟩π = ⟨g,f⟩π.

**Proof.** Write both inner products as expectations using the inner-product expectation formula (FABL.pmfInner_eq_expect). At each x, the integrands agree because f(x)g(x) = g(x)f(x). Thus the expectations, and hence the inner products, are equal.

**Key facts.** `FABL.pmfInner_eq_expect`.
