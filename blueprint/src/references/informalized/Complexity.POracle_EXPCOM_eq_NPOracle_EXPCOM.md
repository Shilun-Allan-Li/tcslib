<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic and Nondeterministic Exponential-Oracle Classes

**Claim.** For the oracle language $\mathrm{EXPCOM}$, deterministic and nondeterministic polynomial-time oracle computation define the same class: $\mathrm{P}^{\mathrm{EXPCOM}}=\mathrm{NP}^{\mathrm{EXPCOM}}$.

**Proof.** Both classes are identified with ordinary exponential time. Specifically, the deterministic class satisfies $\mathrm{P}^{\mathrm{EXPCOM}}=\mathrm{EXP}$ (\texttt{Complexity.POracle_EXPCOM_eq_EXP}), and the nondeterministic class satisfies $\mathrm{NP}^{\mathrm{EXPCOM}}=\mathrm{EXP}$ (\texttt{Complexity.NPOracle_EXPCOM_eq_EXP}). By symmetry of equality, the second identification gives $\mathrm{EXP}=\mathrm{NP}^{\mathrm{EXPCOM}}$; transitivity with the first yields the claimed equality.

**Key facts.** `Complexity.POracle_EXPCOM_eq_EXP`, `Complexity.NPOracle_EXPCOM_eq_EXP`.
