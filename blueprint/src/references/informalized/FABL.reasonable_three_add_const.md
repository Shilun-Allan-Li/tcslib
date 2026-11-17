<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.reasonable_three_add_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adding a Constant Preserves Reasonableness

**Claim.** If a random variable has mean and third moment zero and is reasonable with constant $3$, then adding any constant to it preserves reasonableness with constant $3$.

**Proof.** Let $m_2=\mathbb E[X^2]$ and $m_4=\mathbb E[X^4]$. First, $m_2\ge0$, since it is the expectation of a square (\texttt{FABL.pmfExpectation_nonneg}). Expanding $(c+X)^2$ and using linearity of expectation, the expectation of a constant, and scaling of expectation gives $\mathbb E[(c+X)^2]=c^2+m_2$: the term linear in $X$ vanishes by the mean-zero hypothesis. Likewise, expansion of the fourth power gives $\mathbb E[(c+X)^4]=c^4+6c^2m_2+m_4$; the terms involving $X$ and $X^3$ vanish by the two moment hypotheses. These expectation rules are supplied by \texttt{FABL.pmfExpectation_add}, \texttt{FABL.pmfExpectation_const}, and \texttt{FABL.pmfExpectation_const_mul}. The desired fourth-moment bound now follows from $m_4\le3m_2^2$ and the elementary inequality $c^4+6c^2m_2+3m_2^2\le3(c^2+m_2)^2$, using $m_2\ge0$. Finally, $1\le3$, which is the other condition in the definition of reasonableness.

**Key facts.** `FABL.pmfExpectation_nonneg`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`.
