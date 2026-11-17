<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.ntime_poly_subset_NP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Nondeterministic Time Is in NP

**Claim.** For every $c\in\mathbb N$, every language decidable by a finite nondeterministic Turing machine in time at most a constant multiple of $n^c+1$ belongs to $\mathrm{NP}$.

**Proof.** Let $L$ have a nondeterministic decider $N$ running within $a(n^c+1)$ steps. The polynomial-time choice verifier belongs to $\mathrm P$ (\texttt{Complexity.cont\_choiceVerifier\_mem\_P}). The certificate characterization (\texttt{Complexity.choice\_certificate\_iff}) says that for each input $x$, membership in $L$ is equivalent to the existence of a certificate $u$ of length $(2a)(|x|+1)^c$ such that $x$ followed by $u$ belongs to this verifier language. Taking certificate constant $2a$, exponent $c$, and that verifier as the language in the definition of $\mathrm{NP}$ proves the claim.

**Key facts.** `Complexity.choice_certificate_iff`, `Complexity.cont_choiceVerifier_mem_P`.
