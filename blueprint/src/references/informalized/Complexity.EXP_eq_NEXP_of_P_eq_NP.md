<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.EXP_eq_NEXP_of_P_eq_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Class Equality Collapses Exponential Classes

**Claim.** If $\mathrm{P}=\mathrm{NP}$, then $\mathrm{EXP}=\mathrm{NEXP}$.

**Proof.** One inclusion, $\mathrm{EXP}\subseteq\mathrm{NEXP}$, holds unconditionally (`EXP_subset_NEXP`). For the reverse, take a language in $\mathrm{NEXP}$, witnessed by a polynomial-time verifier $V$ and certificates of the prescribed exponential length. The padding lemma `a3n_pad_mem_NP` constructs a padded language in $\mathrm{NP}$ from this witness. Under $\mathrm{P}=\mathrm{NP}$, that padded language is in $\mathrm{P}$. The unpadding lemma `a3n_unpad_EXP` then recovers the original language as a member of $\mathrm{EXP}$. Thus $\mathrm{NEXP}\subseteq\mathrm{EXP}$, proving equality.

**Key facts.** `Complexity.EXP_subset_NEXP`, `Complexity.a3n_pad_mem_NP`, `Complexity.a3n_unpad_EXP`.
