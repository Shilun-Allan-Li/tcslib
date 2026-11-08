<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpTime.lean :: Complexity.NL_subset_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic Logarithmic Space Runs in Polynomial Time

**Claim.** Every language in nondeterministic logarithmic space belongs to polynomial time.

**Proof.** Let $L\in\mathrm{NL}$. The logarithmic space bound is space-constructible, so the nondeterministic-space-to-deterministic-time theorem places $L$ in a deterministic time class with bound $2^{c(\mathrm{logSpace}(n)+1)}$ for some natural number $c$. It remains to bound this by a polynomial times a constant. Since $\mathrm{logSpace}(n)=\lfloor\log_2 n\rfloor+1$ in the stated convention, we have $2^{\mathrm{logSpace}(n)-1}=2^{\lfloor\log_2 n\rfloor}\le n$ when $n>0$, and the corresponding bound also holds at $n=0$ after replacing $n$ by $n+1$. Hence $2^{\mathrm{logSpace}(n)}\le n+1$. Rewriting the time bound gives
\[
2^{c(\mathrm{logSpace}(n)+1)}=2^{2c}\bigl(2^{\mathrm{logSpace}(n)-1}\bigr)^c\le 2^{2c}(n+1)^c.
\]
The elementary estimate $(n+1)^c\le 2^c(n^c+1)$ therefore bounds the running time by $2^{3c}(n^c+1)$. A language decidable within a constant multiple of $n^c+1$ belongs to $\mathrm{P}$, proving the inclusion.

**Key facts.** `Complexity.spaceConstructible_logSpace`, `Complexity.NSPACE_subset_exp_dtime`, `Complexity.succ_pow_le`, `Complexity.mem_P_of_dtime_le`.
