<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierFormulas.lean :: FABL.noiseStability_dictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator Noise Stability

**Claim.** For every coordinate $i$, the dictator's noise stability at correlation $\rho$ is $\rho$.

**Proof.** The real-valued dictator agrees pointwise with the parity character supported on the singleton set $\{i\}$ (\texttt{dictator_toReal_eq_monomial_singleton} and \texttt{parityFunction_toReal}). The stability of a parity character on a set $S$ is $\rho^{|S|}$ (\texttt{noiseStability_parityFunction}); taking $S=\{i\}$ gives $\rho^1=\rho$.

**Key facts.** `FABL.dictator_toReal_eq_monomial_singleton`, `FABL.parityFunction_toReal`, `FABL.noiseStability_parityFunction`.
