<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierFormulas.lean :: FABL.noiseStability_parityFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability of Parity

**Claim.** For every $\rho\in[-1,1]$ and every coordinate set $S$, the noise stability of the parity function indexed by $S$ is $\rho^{|S|}$.

**Proof.** The real-valued form of this parity function is the monomial indexed by $S$ (`parityFunction_toReal`). The monomial stability formula then gives $\rho^{|S|}$ (`noiseStability_monomial`).

**Key facts.** `FABL.parityFunction_toReal`, `FABL.noiseStability_monomial`.
