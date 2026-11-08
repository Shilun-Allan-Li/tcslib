<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.tendsto_shiftedBinomialProbability_div_oddMajorityInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Binomial Probability Asymptotics

**Claim.** For fixed natural numbers $c$ and $j$ with $j\le c$, the ratio $P_m/I_m$ tends to $1$ as $m\to\infty$.

**Proof.** Proceed by induction on $c$, keeping $j$ general. When $c=0$, the condition forces $j=0$, and the shifted binomial probability equals the odd-majority influence, so the ratio is identically $1$; the influence is positive, ensuring the quotient is defined. Now suppose the result holds for $c$. If $j=c+1$, the diagonal recurrence expresses the probability with parameters $(c+1,c+1)$ as the probability with parameters $(c,c)$ times $(2m+c+1)/(2(m+c+1))$. The first ratio tends to $1$ by induction and the factor tends to $1$ by the shifted diagonal factor limit; their product tends to $1$. In the other case, $j\le c$. The same-parameter recurrence expresses the probability with parameters $(c+1,j)$ as the probability with parameters $(c,j)$ times $(2m+c+1)/(2(m+c+1-j))$. Induction gives limit $1$ for the probability-to-influence ratio, and the shifted same-factor limit gives limit $1$ for the additional factor. Their product again tends to $1$. Positivity of the influence justifies the quotient manipulations in both cases.

**Key facts.** `FABL.shiftedBinomialProbability_zero`, `FABL.oddMajorityInfluence_pos`, `FABL.shiftedBinomialProbability_succ_diagonal`, `FABL.tendsto_shiftedBinomialDiagonalFactor`, `FABL.shiftedBinomialProbability_succ_same`, `FABL.tendsto_shiftedBinomialSameFactor`.
