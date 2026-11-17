<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.NPOracle_EXPCOM_eq_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic Exponential-Oracle Time Equals Exponential Time

**Claim.** The class of languages decidable in nondeterministic polynomial time with oracle $\mathrm{EXPCOM}$ is exactly $\mathrm{EXP}$.

**Proof.** We prove the two inclusions. First, the established simulation theorem places every language in $\mathrm{NPOracle}(\mathrm{EXPCOM})$ in $\mathrm{EXP}$. For the reverse inclusion, deterministic polynomial time with oracle $\mathrm{EXPCOM}$ is contained in nondeterministic polynomial time with the same oracle, since a nondeterministic machine can follow the deterministic computation. The established equality $\mathrm{POracle}(\mathrm{EXPCOM})=\mathrm{EXP}$ then shows that every language in $\mathrm{EXP}$ belongs to $\mathrm{NPOracle}(\mathrm{EXPCOM})$. The inclusions in both directions give the claimed equality.

**Key facts.** `Complexity.NPOracle_EXPCOM_subset_EXP`, `Complexity.POracle_subset_NPOracle`, `Complexity.POracle_EXPCOM_eq_EXP`.
