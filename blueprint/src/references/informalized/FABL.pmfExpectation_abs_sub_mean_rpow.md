<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.pmfExpectation_abs_sub_mean_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Moments of Sign Deviations

**Claim.** If $f$ takes values in $\{-1,1\}$, then its absolute deviation moment of order $p$ equals $a(2b)^p+b(2a)^p$, where $a$ and $b$ are the probabilities of the values $1$ and $-1$.

**Proof.** Let $a$ and $b$ be the masses of the positive and negative values. They are nonnegative (\texttt{pmfSignPlusMass\_nonneg}, \texttt{pmfSignMinusMass\_nonneg}) and sum to $1$ (\texttt{pmfSignPlusMass\_add\_minus}). The mean is $a-b$ (\texttt{pmfExpectation\_eq\_signPlusMass\_sub\_minus}). Consequently, the deviation from the mean is $2b$ when $f=1$, and $-2a$ when $f=-1$. Taking absolute values and raising to the real power $p$ yields $(2b)^p$ and $(2a)^p$. Pointwise, the resulting function is the sum of the indicator of $f=1$ times $(2b)^p$ and the indicator of $f=-1$ times $(2a)^p$. Linearity of expectation and pulling out constants then give $a(2b)^p+b(2a)^p$ (\texttt{pmfExpectation\_add}, \texttt{pmfExpectation\_mul\_const}).

**Key facts.** `FABL.pmfSignPlusMass_nonneg`, `FABL.pmfSignMinusMass_nonneg`, `FABL.pmfSignPlusMass_add_minus`, `FABL.pmfExpectation_eq_signPlusMass_sub_minus`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_mul_const`.
