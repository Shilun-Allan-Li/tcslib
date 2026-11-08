<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.exercise9_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure of translation stability

**Claim.** For any $1<b<B$, there are a probability distribution $p$ on the two-point space and a function $X$ such that $X$ satisfies the stated moment condition with constant $b$, while $1+X$ fails the condition with constant $B$.

**Proof.** Let $q=(b-1)/(2bB)$, which is positive. The assumptions imply $q<1/B<1$ and $q<1-1/b$. Choose the biased two-point distribution with mass $q$ on the point where $X=0$ and mass $1-q$ on the point where $X=-1$. Thus $X$ is a negative-one-or-zero Bernoulli variable. Its second and fourth moments are both $1-q$ (\texttt{FABL.pmfExpectation\_finiteBernoulli\_negOneOrZero\_even}). Since $q<1-1/b$, we have $1/b<1-q$, or $1<b(1-q)$. Multiplying by the nonnegative $1-q$ shows $1-q\le b(1-q)^2$. Together with $1\le b$, this proves that $X$ is reasonable with constant $b$.

After translation, $1+X$ is zero at the point formerly carrying value $-1$, and one at the point formerly carrying value zero. Its second and fourth moments are both $q$ (\texttt{FABL.pmfExpectation\_finiteBernoulli\_zeroOne\_pow}). If it were reasonable with constant $B$, the moment inequality would give $q\le Bq^2$. Because $q>0$, this implies $1\le Bq$. But $q<1/B$ gives $Bq<1$, a contradiction. Hence the translated function fails the required condition.

**Key facts.** `FABL.pmfExpectation_finiteBernoulli_negOneOrZero_even`, `FABL.pmfExpectation_finiteBernoulli_zeroOne_pow`.
