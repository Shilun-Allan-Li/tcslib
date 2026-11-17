<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TimeHierarchy/Separation.lean :: Complexity.P_ssubset_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict polynomial–exponential containment

**Claim.** The class $\mathsf{P}$ is a proper subset of $\mathrm{EXP}$.

**Proof.** 1. Polynomial time is contained in exponential time by $\texttt{Complexity.P\_subset\_EXP}$. To prove properness, consider the diagonal language $D=\operatorname{diagLang}(n\mapsto 2^n)$. Since $n\mapsto 2^n$ is time-constructible, the diagonal time-hierarchy construction places $D$ in time $2^n+1$ (\texttt{Complexity.TimeHierarchy.diagLang\_mem\_DTIME} and \texttt{Complexity.timeConstructible\_two\_pow}). This bound is covered by the exponential-time class, so $D\in\mathrm{EXP}$.

2. If $\mathsf{P}=\mathrm{EXP}$, then $D\in\mathsf{P}$. Unpacking the union defining $\mathsf{P}$ would give some exponent $k$ for which $D$ is decidable in time $n^k+1$. The diagonal non-membership theorem rules this out once its growth hypothesis is verified (\texttt{Complexity.TimeHierarchy.diagLang\_not\_mem\_DTIME}).

3. For any multiplicative constant $A$, the eventual bound $A(n^k+1+n+1)^2\le 2^n$ holds for all sufficiently large $n$ (\texttt{Complexity.eventually\_poly\_sq\_le\_two\_pow}). Choose $n$ beyond that threshold and beyond the cutoff in the purported time bound. This supplies exactly the growth condition required by the diagonal theorem, contradicting the assumed polynomial-time decision of $D$. Thus the inclusion is strict.

**Key facts.** `Complexity.P_subset_EXP`, `Complexity.TimeHierarchy.diagLang_mem_DTIME`, `Complexity.timeConstructible_two_pow`, `Turing.FinTM.ComputesInTime.mono`, `Complexity.TimeHierarchy.diagLang_not_mem_DTIME`, `Complexity.eventually_poly_sq_le_two_pow`.
