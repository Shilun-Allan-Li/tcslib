<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierWeightLimits.lean :: FABL.majority_binomial_factorization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binomial Factorization

**Claim.** For natural numbers $m$ and $j$ with $j\le m$, the stated quotient of binomial coefficients factors as $\binom{2j}{j}\binom{2(m-j)}{m-j}$.

**Proof.** Rewrite each binomial coefficient using $\binom{a}{b}=a!/(b!(a-b)!)$, then use $2m-m=m$, $2m-2j=2(m-j)$, and $2j-j=j$. The left side becomes
\[
\frac{\bigl(m!/(j!(m-j)!)\bigr)^2\,(2m)!/(m!m!)}{(2m)!/((2j)!(2(m-j))!)}.
\]
Canceling the nonzero factorial factors leaves $\frac{(2j)!}{j!j!}\frac{(2(m-j))!}{(m-j)!(m-j)!}$, which is precisely the right side.
