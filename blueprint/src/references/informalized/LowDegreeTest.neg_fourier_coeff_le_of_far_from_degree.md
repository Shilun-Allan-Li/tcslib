<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.neg_fourier_coeff_le_of_far_from_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier bound from distance to low degree

**Claim.** If a Boolean function is $\varepsilon$-far from degree at most $d$, where $d\ge1$, then every Fourier coefficient of its $\pm1$ lift satisfies $-\widehat{F}(S)\le 1-2\varepsilon$.

**Proof.** Fix $S$. By the degree bound for negated Walsh characters (`LowDegreeTest.neg_char_is_degree_le`), the function represented by $-\chi_S$ is an admissible degree-at-most-$d$ comparison function. Convert this sign-valued function back to a Boolean function $g$; its lift is $-\chi_S$, and it retains the stated degree bound. The far-from-degree hypothesis gives $\operatorname{dist}(f,g)\ge\varepsilon$. At each input, the product of the two sign lifts is $1$ when the Boolean values agree and $-1$ when they disagree. Averaging yields $\langle F,\operatorname{lift}(g)\rangle=1-2\operatorname{dist}(f,g)$. Since $\operatorname{lift}(g)=-\chi_S$, this inner product equals $-\widehat{F}(S)$. Therefore $-\widehat{F}(S)=1-2\operatorname{dist}(f,g)\le1-2\varepsilon$.

**Key facts.** `LowDegreeTest.neg_char_is_degree_le`.
