<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.corollary4_32_of_halfSwitching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Agreement Excludes Small Circuits

**Claim.** Assuming a half-switching bound, if a depth-$d$ circuit agrees with full parity with probability at least $1/2+\varepsilon_0$, then every $s>1$ whose LMN degree cutoff at parameter $2\varepsilon_0^2$ is below $n$ must be smaller than the circuit’s size.

**Proof.** First, the agreement probability is at most one, since it is a probability. Together with the assumed lower bound, this implies $\varepsilon_0\le 1/2$, so $\eta=2\varepsilon_0^2$ is positive and at most $1/2$.

Now fix $s>1$ with the stated cutoff condition, and suppose for contradiction that the circuit has size at most $s$. It is then a circuit of its own depth and of size at most $s$, so the LMN theorem under the half-switching hypothesis (`lmn_theorem_of_halfSwitching`) says its Fourier spectrum is concentrated up to the cutoff $k=\mathrm{lmnDegreeCutoff}(d,s,\eta)$, with error parameter $\eta$.

The parity-agreement concentration bound (`parityAgreement_forces_concentration_cutoff`) applies: its error condition holds because $2\varepsilon_0^2<4\varepsilon_0^2$. It forces $n\le k$. This contradicts the assumed $k<n$, so the circuit’s size must exceed $s$.

**Key facts.** `FABL.uniformProbability_le_one`, `FABL.lmn_theorem_of_halfSwitching`, `FABL.parityAgreement_forces_concentration_cutoff`.
