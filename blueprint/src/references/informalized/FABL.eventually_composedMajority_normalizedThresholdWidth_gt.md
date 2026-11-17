<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.eventually_composedMajority_normalizedThresholdWidth_gt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composed majority threshold width

**Claim.** For every $\epsilon\in(0,1/4)$, the normalized threshold width of the composed majority family is greater than $1/2-\sqrt\epsilon$ for all sufficiently large $m$.

**Proof.** 1. Set $a$ to the composed-majority threshold probe at $\epsilon$, and set $b=1-a$. The probe lies in $(0,1/2)$, while $b$ lies in $(1/2,1)$; also $\epsilon<a^2$. The two probability-limit results say that at fixed parameters below and above $1/2$, respectively, the composed-majority probabilities converge to $p^2$ and $1-(1-p)^2$ ($\texttt{tendsto\_composedMajority\_probability\_of\_lt\_half}$ and $\texttt{tendsto\_composedMajority\_probability\_of\_half\_lt}$). Consequently, for all sufficiently large $m$, the probability at $a$ exceeds $\epsilon$, and the probability at $b$ is less than $1-\epsilon$. The latter follows from $1-(1-b)^2=1-a^2<1-\epsilon$.

2. Let $p_0$ and $p_1$ be the lower and upper threshold parameters at levels $\epsilon$ and $1-\epsilon$. They lie in $(0,1)$ and their probabilities equal those levels ($\texttt{biasedProbabilityLevel\_mem\_Ioo}$, $\texttt{biasedMinusProbabilityPolynomial\_thresholdLowerParameter}$, and $\texttt{biasedMinusProbabilityPolynomial\_thresholdUpperParameter}$). The probability polynomial is strictly increasing on $[0,1]$ for this monotone, nonconstant function ($\texttt{strictMonoOn\_biasedMinusProbabilityPolynomial}$). Thus the probability comparison at $a$ forces $p_0<a$, and the comparison at $b$ forces $b<p_1$.

3. The normalized width equals the ordinary threshold width for this family ($\texttt{normalizedThresholdWidth\_composedMajority\_eq\_thresholdWidth}$), so it is $p_1-p_0$. The inequalities just proved imply $p_1-p_0>b-a=1-2a$. The probe identity $1-2a=1/2-\sqrt\epsilon$ gives the desired strict lower bound.

**Key facts.** `FABL.composedMajorityThresholdProbe_mem_Ioo`, `FABL.one_sub_composedMajorityThresholdProbe_mem_Ioo`, `FABL.epsilon_lt_composedMajorityThresholdProbe_sq`, `FABL.tendsto_composedMajority_probability_of_lt_half`, `FABL.tendsto_composedMajority_probability_of_half_lt`, `FABL.biasedProbabilityLevel_mem_Ioo`, `FABL.biasedMinusProbabilityPolynomial_thresholdLowerParameter`, `FABL.biasedMinusProbabilityPolynomial_thresholdUpperParameter`, `FABL.strictMonoOn_biasedMinusProbabilityPolynomial`, `FABL.normalizedThresholdWidth_composedMajority_eq_thresholdWidth`, `FABL.one_sub_two_mul_composedMajorityThresholdProbe`.
