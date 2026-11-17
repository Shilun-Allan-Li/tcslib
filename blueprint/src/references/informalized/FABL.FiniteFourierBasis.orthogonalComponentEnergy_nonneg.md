<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.orthogonalComponentEnergy_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative component energy

**Claim.** The squared norm of any orthogonal Fourier component, measured in the product probability inner product, is nonnegative.

**Proof.** The energy is the product inner product of the component with itself. The nonnegativity of a probability-weighted inner product on a function paired with itself ($\texttt{FABL.pmfInner_self_nonneg}$) therefore gives the result.

**Key facts.** `FABL.pmfInner_self_nonneg`.
