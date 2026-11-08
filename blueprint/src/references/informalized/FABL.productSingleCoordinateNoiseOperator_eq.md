<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.productSingleCoordinateNoiseOperator_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear form of the single-coordinate noise operator

**Claim.** The single-coordinate noise operator can be written as $\rho f+(1-\rho)$ times the coordinate projection of $f$.

**Proof.** Expand the definitions: the operator is the coordinate projection plus $\rho$ times the coordinate Laplacian, and the Laplacian is $f$ minus that projection. Distributing the scalar gives $E_i f+\rho(f-E_i f)=\rho f+(1-\rho)E_i f$, as claimed.
