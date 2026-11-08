<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.POracle_EXPCOM_eq_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle Exponential-Time Characterization

**Claim.** Deterministic polynomial time with oracle $\mathrm{EXPCOM}$ equals deterministic exponential time: $\mathrm{P}^{\mathrm{EXPCOM}}=\mathrm{EXP}$.

**Proof.** For one inclusion, deterministic polynomial time with any oracle is contained in nondeterministic polynomial time with that oracle (`Complexity.POracle_subset_NPOracle`), and nondeterministic polynomial time with oracle $\mathrm{EXPCOM}$ is contained in $\mathrm{EXP}$ (`Complexity.NPOracle_EXPCOM_subset_EXP`). Thus $\mathrm{P}^{\mathrm{EXPCOM}}\subseteq\mathrm{EXP}$. In the reverse direction, exponential time is contained in deterministic polynomial time with oracle $\mathrm{EXPCOM}$ (`Complexity.EXP_subset_POracle_EXPCOM`). The two inclusions give equality.

**Key facts.** `Complexity.POracle_subset_NPOracle`, `Complexity.NPOracle_EXPCOM_subset_EXP`, `Complexity.EXP_subset_POracle_EXPCOM`.
